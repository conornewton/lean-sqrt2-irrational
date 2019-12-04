/-
  Author: Conor Newton
  Email: conornewton@gmail.com

  I promise that I will get around to fixing this up eventually, it is a bit messy!
-/

open nat
open int
open classical

local attribute [instance] classical.prop_decidable

@[simp]
def even (n : nat) := ∃ a : nat, n = 2 * a
@[simp]
def odd  (n : nat) := ¬ even n

--I dont like haveing to use leans gcd and coprime definition, mine is better!
@[simp]
def relatively_prime (a b : nat) := ∀ d : nat, (∃ m n : nat, a = d * m ∧ b = d * n) → d = 1

--Every natural number is even or odd.
lemma even_or_odd (n : nat) : even n ∨ odd n := em (even n)

--Basic congruency
lemma succ_eq_succ {a b : nat} : a = b → succ a = succ b := congr_arg succ

--Useful lemma 
lemma odd_shape_neq_even_shape : ∀ a b : nat, 2 * a ≠ 2 * b + 1:=
begin
  intros a b,
  intro h,
  have p, from congr_arg (λ x, x % 2) h,
  rw mul_mod_right at p,
  rw add_comm at p,
  rw add_mul_mod_self_left at p,
  have h : 1 < 2, from succ_lt_succ zero_lt_one,
  rw mod_eq_of_lt h at p,
  simp at p,
  exact p,
end

--odd numbers are of the form 2n + 1
theorem odd_form {a : nat} : odd a → ∃ x : nat, a = 2 * x + 1 :=
begin
  induction a with n ih,
    --base case
    have h' : even 0 , from ⟨ 0, refl 0⟩,
    contradiction,
    --induction step
    cases even_or_odd n,
      --even
      intro q,
      simp at h,
      cases h with a p,
      have c : succ n = 2 * a + 1, from succ_eq_succ p,
      exact ⟨a, c⟩,
      --odd
      intro q,
      have h2 : ∃ x : nat, n = 2 * x + 1, from ih h,
      cases h2 with  x h2,
      have h3 : succ n = 2 * x + 2, from (congr_arg succ) h2,
      rw [←mul_one 2, mul_assoc, ←left_distrib 2 (1 * x) 1] at h3,
      have h4 : even (succ n), from ⟨ 1 * x + 1, h3⟩,
      contradiction, -- we have shown succ is both odd and even,
end

--reverse of the previous theorem
theorem form_odd {a : nat} : (∃ x : nat, a = 2 * x + 1) → odd a :=
begin
  intro h,
  cases h with x h,
  intro a,
  simp at a,
  cases a with y p,
  rw h at p,
  have p', from eq.symm p,
  have p'', from  odd_shape_neq_even_shape y x,
  contradiction,
end

--not sure im using this
theorem succ_odd_even (n : nat) : odd n → even (n + 1) :=
begin
  intro h,
  have h2 : ∃ x, n = 2 * x + 1, from odd_form h,
  cases h2 with  x h2,
  have h3 : succ n = 2 * x + 2, from (congr_arg succ) h2,
  rw [←mul_one 2, mul_assoc, ←left_distrib 2 (1 * x) 1] at h3,
  have h4 : even (succ n), from ⟨1 * x + 1, h3⟩,
  exact h4,
end

lemma odd_squared_odd (n : nat) : odd n → odd (n * n) :=
begin
  intro h,
  have p, from odd_form h,
  cases p with x p,
  have p' : n * n = (2 * x + 1) * (2 * x + 1), from congr_arg (λ x, x * x) p,
  rw right_distrib at p',
  rw left_distrib at p',
  rw mul_one at p',
  rw one_mul at p',
  rw add_comm at p',
  rw mul_assoc at p',
  rw ←left_distrib at p',
  rw add_comm at p',
  rw ←add_assoc at p',
  rw ←left_distrib at p',
  have o : odd (n * n), from form_odd ⟨ x* ( 2 * x) + x + x, p'⟩,
  exact o,
end

--Just the contrapositive of the above
--How do i just use the contrapositive?
lemma even_squared_even (n : nat) : even (n * n) → even n := 
begin
  intro a,
  by_contradiction h,
  have o : odd n, from h, --what is the easier way of doing this
  have od : odd (n * n), from odd_squared_odd n o,
  contradiction,  
end

--How can i tidy this up?
lemma evens_not_coprime {a b : nat} : even a → even b → ¬ relatively_prime a b :=
begin
  intros e1 e2,
  simp, 
  intro h,

  simp at e1 e2,
  cases e1 with x e1,
  cases e2 with y e2,

  have h', from h 2,

  have p : ∃ m n : nat, a = 2 * m ∧ b = 2 * n, from ⟨x, ⟨y, and.intro e1 e2 ⟩⟩,
  have c : 2 = 1, from h' p,
  have c' : 2 ≠ 1, from succ_ne_self 1,
  simp at c',
  contradiction,
end

theorem sqrt2_irrational (a b : nat) : b ≠ 0 ∧ relatively_prime a b → a * a ≠ 2 * b * b :=
begin
  intro h,
  by_contradiction f,
  simp at f,
  have g :  a * a = 2 * b * b, from (decidable.of_not_not f),
  cases even_or_odd a with j k,
    --a is even
    begin --aim to contradict gcd a b = 1
      simp at j,
      cases j with c j,
        rw j at g,
        rw [mul_assoc] at g,
        --how else can i flip an equation??
        have h2 : 2 * b * b = 2 * (c * (2 * c)), from eq.symm g,
        rw [mul_assoc] at g,
        have p : 2 > 0,
          begin
             cases eq_zero_or_pos 2, 
               cases h_1,
               exact h_1,
          end,
        have h3 : c * (2 * c) = b * b, from (eq_of_mul_eq_mul_left p g),
        rw [mul_comm] at h3,
        rw [mul_assoc] at h3,

        have h4 : 2 * (c * c) % 2 = b * b % 2, from (congr_arg (λ x, x % 2)) h3,
        rw [mul_mod_right] at h4,
        
        ----FIX HERE AND ABOVE
        have h4 : even (b * b), from ⟨c * c, eq.symm h3⟩,
        have h5 : even b, from even_squared_even b h4,
        simp at h5,
        cases h5 with d k,
        have ea : even a, from ⟨c, j⟩,
        have eb : even b, from ⟨d, k⟩,
        have h6 : ¬ relatively_prime a b, from (evens_not_coprime ea eb),
        have h7 : relatively_prime a b, from h.right,
        contradiction,
    end,
    --a is odd
    begin
      --We know that a^2 is even so we find a contradiciton.
      cases odd_form k with x l,
      rw l at g,
      have g2 : (2 * x + 1) * (2 * x + 1) % 2 = (2 * b * b) % 2, from (congr_arg (λ x, x % 2)) g,
      rw [mul_assoc] at g2,
      rw [mul_mod_right 2 (b*b)] at g2,
      rw [left_distrib] at g2,
      rw [right_distrib] at g2,
      rw [mul_one] at g2,
      rw [one_mul] at g2,
      rw mul_assoc at g2,
      rw ←add_assoc at g2,
      rw ←left_distrib at g2,
      rw ←left_distrib at g2,
      rw add_comm at g2,
      rw [add_mul_mod_self_left] at g2,
      rw [mod_eq_of_lt (lt.base 1)] at g2,
      contradiction,
    end,
end
