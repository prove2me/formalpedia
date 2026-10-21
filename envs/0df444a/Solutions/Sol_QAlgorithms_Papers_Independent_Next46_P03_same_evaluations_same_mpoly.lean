-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P03.same_evaluations_same_mpoly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:51:36.23803+00:00
-- url     : https://prove2.me/submissions/b145edb5-0429-438c-9be7-6a67559f6ce7

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P03

open QAlgorithms.Papers.Independent.Next46.P03

theorem g62r_eval_trunc (p : MvPolynomial ℕ ℝ) (N : ℕ) (hN : ∀ i ∈ p.vars, i < N) (x : ℕ → ℝ) :
    MvPolynomial.eval x p = evalMpoly ((List.range N).map x) p := by
  unfold evalMpoly
  refine MvPolynomial.hom_congr_vars ?_ ?_ rfl
  · ext r; simp
  · intro i hi _
    simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.eval_X]
    rw [List.getD_eq_getElem _ _ (by simpa using hN i hi)]
    simp

theorem solution (p q : MvPolynomial ℕ ℝ)
    (h : ∀ xs : List ℝ, evalMpoly xs p = evalMpoly xs q) :
    p = q := by
  classical
  let N := (p.vars ∪ q.vars).sup id + 1
  have hN : ∀ i ∈ p.vars ∪ q.vars, i < N := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  apply MvPolynomial.funext
  intro x
  rw [g62r_eval_trunc p N (fun i hi => hN i (Finset.mem_union_left _ hi)) x,
    g62r_eval_trunc q N (fun i hi => hN i (Finset.mem_union_right _ hi)) x]
  exact h _
