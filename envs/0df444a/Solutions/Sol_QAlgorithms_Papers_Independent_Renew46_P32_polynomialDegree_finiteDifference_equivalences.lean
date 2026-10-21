-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.polynomialDegree_finiteDifference_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:12:15.622297+00:00
-- url     : https://prove2.me/submissions/f97d540a-42f5-4895-9769-4a56d4e0b545

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

open QAlgorithms.Papers.Independent.Renew46.P32

universe u

section
variable {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B]

theorem g66b_lin_succ (q : A → B) (x : A) (k : ℕ) (h : Fin (k + 1) → A) :
    linearization q x (k + 1) h =
      linearization (fun y => q (y + h 0) - q y) x k (Fin.tail h) := rfl

theorem g66b_lin_sub (k : ℕ) : ∀ (q1 q2 : A → B) (x : A) (h : Fin k → A),
    linearization (fun y => q1 y - q2 y) x k h =
      linearization q1 x k h - linearization q2 x k h := by
  induction k with
  | zero => intro q1 q2 x h; rfl
  | succ k ih =>
    intro q1 q2 x h
    rw [g66b_lin_succ, g66b_lin_succ, g66b_lin_succ, ← ih]
    congr 1; funext y; abel

theorem g66b_lin_congr (k : ℕ) (q1 q2 : A → B) (hq : q1 = q2) (x : A) (h : Fin k → A) :
    linearization q1 x k h = linearization q2 x k h := by subst hq; rfl

theorem g66b_lin_comm (k : ℕ) : ∀ (q : A → B) (a x : A) (h : Fin k → A),
    linearization (fun y => q (y + a) - q y) x k h =
      linearization q (x + a) k h - linearization q x k h := by
  induction k with
  | zero => intro q a x h; rfl
  | succ k ih =>
    intro q a x h
    rw [g66b_lin_succ, g66b_lin_succ, g66b_lin_succ, ← ih]
    apply g66b_lin_congr; funext y
    rw [add_right_comm]; abel

theorem g66b_slot0 (k : ℕ) (q : A → B) (x a b : A) (t : Fin k → A) :
    linearization q x (k + 2) (Fin.cons b (Fin.cons a t)) =
      linearization q x (k + 1) (Fin.cons (a + b) t) -
        linearization q x (k + 1) (Fin.cons a t) -
        linearization q x (k + 1) (Fin.cons b t) := by
  have e : ∀ (q' : A → B) c, linearization q' x (k + 1) (Fin.cons c t) =
      linearization (fun y => q' (y + c) - q' y) x k t := fun _ _ => rfl
  have e2 : linearization q x (k + 2) (Fin.cons b (Fin.cons a t)) =
      linearization (fun y => q (y + b) - q y) x (k + 1) (Fin.cons a t) := rfl
  rw [e2, e, e, e, e, ← g66b_lin_sub, ← g66b_lin_sub]
  apply g66b_lin_congr; funext y
  rw [← add_assoc]; abel

theorem g66b_upd0 {n : ℕ} (h : Fin (n + 1) → A) (c : A) :
    Function.update h 0 c = Fin.cons c (Fin.tail h) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [Fin.tail, Function.update_of_ne (Fin.succ_ne_zero j)]

theorem g66b_case0 (k : ℕ) (q : A → B) (x : A) (h : Fin (k + 1) → A) (a b : A) :
    linearization q x (k + 1) (Function.update h 0 (a + b)) =
      linearization q x (k + 1) (Function.update h 0 a) +
        linearization q x (k + 1) (Function.update h 0 b) +
        linearization q x (k + 2) (Fin.cons b (Fin.cons a (Fin.tail h))) := by
  rw [g66b_slot0, g66b_upd0, g66b_upd0, g66b_upd0]
  abel

theorem g66b_upds (k : ℕ) (q : A → B) (x : A) (h : Fin (k + 2) → A) (j : Fin (k + 1)) (c : A) :
    linearization q x (k + 2) (Function.update h j.succ c) =
      linearization (fun y => q (y + h 0) - q y) x (k + 1) (Function.update (Fin.tail h) j c) := by
  rw [g66b_lin_succ, Fin.tail_update_succ,
    Function.update_of_ne (Fin.succ_ne_zero j).symm]

theorem g66b_defect (k : ℕ) : ∀ (q : A → B) (x : A) (h : Fin (k + 1) → A) (i : Fin (k + 1))
    (a b : A), ∃ h' : Fin (k + 2) → A,
    linearization q x (k + 1) (Function.update h i (a + b)) =
      linearization q x (k + 1) (Function.update h i a) +
        linearization q x (k + 1) (Function.update h i b) + linearization q x (k + 2) h' := by
  induction k with
  | zero =>
    intro q x h i a b
    refine Fin.cases ?_ (fun j => j.elim0) i
    exact ⟨_, g66b_case0 0 q x h a b⟩
  | succ k ih =>
    intro q x h i a b
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨_, g66b_case0 _ q x h a b⟩
    · obtain ⟨h'', hh⟩ := ih (fun y => q (y + h 0) - q y) x (Fin.tail h) j a b
      refine ⟨Fin.cons (h 0) h'', ?_⟩
      rw [g66b_upds, g66b_upds, g66b_upds, hh]
      rfl
theorem g66b_split {n : ℕ} (g : Fin (n + 2) → A) :
    g = Fin.cons (g 0) (Fin.cons (g 1) (Fin.tail (Fin.tail g))) := by
  conv_lhs => rw [← Fin.cons_self_tail g, ← Fin.cons_self_tail (Fin.tail g)]
  rfl

theorem g66b_madd_zero (k : ℕ) (q : A → B) (x : A)
    (hm : IsMultiadditive (linearization q x (k + 1))) (g : Fin (k + 2) → A) :
    linearization q x (k + 2) g = 0 := by
  rw [g66b_split g, g66b_slot0]
  have := hm 0 (Fin.cons (g 1) (Fin.tail (Fin.tail g))) (g 1) (g 0)
  rw [g66b_upd0, g66b_upd0, g66b_upd0, Fin.tail_cons] at this
  rw [this]; abel
end

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]

variable {E : Type u} [AddCommGroup E] [Module K E]

variable {F : Type u} [AddCommGroup F] [Module K F]

theorem solution
    {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B]
    (q : A → B) (k : ℕ) (hk : 0 < k) :
    List.TFAE [
      (∀ x : A, ∀ h : Fin (k + 1) → A, linearization q x (k + 1) h = 0),
      (∀ h : Fin (k + 1) → A, linearization q 0 (k + 1) h = 0),
      (∀ x : A, IsMultiadditive (linearization q x k)),
      IsMultiadditive (linearization q 0 k)
    ] := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  tfae_have 1 → 3 := by
    intro h1 x i h a b
    obtain ⟨h', hh⟩ := g66b_defect k q x h i a b
    rw [hh, h1 x h', add_zero]
  tfae_have 3 → 4 := fun h => h 0
  tfae_have 4 → 2 := fun h g => g66b_madd_zero k q 0 h g
  tfae_have 2 → 1 := by
    intro h2 x h
    have Z : ∀ g : Fin (k + 3) → A, linearization q 0 (k + 3) g = 0 := by
      intro g
      rw [g66b_split g, g66b_slot0, h2, h2, h2]; simp
    have e := g66b_lin_comm (k + 2) q x 0 h
    have e2 : linearization (fun y => q (y + x) - q y) 0 (k + 2) h =
        linearization q 0 (k + 3) (Fin.cons x h) := rfl
    rw [e2, Z, zero_add, h2] at e
    exact (sub_eq_zero.mp e.symm)
  tfae_finish

end AlgebraicDefinitions
