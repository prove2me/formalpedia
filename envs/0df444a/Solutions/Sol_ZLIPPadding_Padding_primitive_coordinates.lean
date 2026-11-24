-- Prove2me | solution 1 for ZLIPPadding.Padding.primitive_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:55:59.281153+00:00
-- url     : https://prove2.me/submissions/5c23ea07-9c57-41a1-af89-9cd881c4a606

import Definitions.Def_ZLIPPadding_Padding_GramModel

set_option autoImplicit false

open ZLIPPadding.Padding

private lemma dvd_foldl_gcd (d : ℕ) (l : List ℕ) (g : ℕ) :
    d ∣ l.foldl Nat.gcd g ↔ d ∣ g ∧ ∀ x ∈ l, d ∣ x := by
  induction l generalizing g with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, Nat.dvd_gcd_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

private lemma dvd_coordGcd {n : ℕ} (d : ℕ) (a : ZVec n) :
    d ∣ coordGcd a ↔ ∀ i, (d : ℤ) ∣ a i := by
  unfold coordGcd
  rw [dvd_foldl_gcd]
  simp only [dvd_zero, true_and, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff, Int.natCast_dvd]

private lemma coordGcd_dvd_mulVec {n : ℕ} (M : ZMat n) (a : ZVec n) :
    coordGcd a ∣ coordGcd (M.mulVec a) := by
  rw [dvd_coordGcd]
  have h := (dvd_coordGcd (coordGcd a) a).1 dvd_rfl
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (h j) _

theorem solution (n : ℕ) (hn : 0 < n) (M : ZMat n)
    (hM : Unimodular M) (a : ZVec n) (ha : a ≠ 0) :
    coordGcd (M.mulVec a) = coordGcd a := by
  obtain ⟨W, -, hWM⟩ := hM
  apply Nat.dvd_antisymm
  · have := coordGcd_dvd_mulVec W (M.mulVec a)
    rwa [Matrix.mulVec_mulVec, hWM, Matrix.one_mulVec] at this
  · exact coordGcd_dvd_mulVec M a
