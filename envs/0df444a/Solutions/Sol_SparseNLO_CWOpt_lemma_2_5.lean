-- Prove2me | solution 1 for SparseNLO.CWOpt.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:17:10.495821+00:00
-- url     : https://prove2.me/submissions/218722b1-7430-4a70-b31f-8e1a53eb3d04

import Mathlib
import Definitions.Def_SparseNLO_CWOpt_Setting

open SparseNLO.CWOpt
open scoped RealInnerProductSpace

private lemma coord_min {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hm : ∀ t : ℝ, f x ≤ f (x + EuclideanSpace.single i t)) :
    gradient f x i = 0 := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have he (t : ℝ) : t • e = EuclideanSpace.single i t := by
    ext j
    simp [e, PiLp.single_apply]
  have hd := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x)
  have hm' : IsLocalMin (fun t : ℝ => f (x + t • e)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change f (x + (0 : ℝ) • e) ≤ f (x + t • e)
    rw [zero_smul, add_zero, he]
    exact hm t
  have hh := hm'.hasDerivAt_eq_zero hd
  simpa [← inner_gradient_left, e, EuclideanSpace.inner_single_right] using hh

theorem solution {n s : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x) (hs : 0 < s) (hsn : s < n)
    (xstar : EuclideanSpace ℝ (Fin n)) (hx : xstar ∈ Cs n s) (hcw : IsCWMin f s xstar) :
    IsBF f s xstar := by
  refine ⟨hx, ?_, ?_⟩
  · intro hlt
    rcases hcw.2 with h | h
    · ext i
      exact coord_min f hf xstar i (h.2 i)
    · omega
  · intro heq i hi
    rcases hcw.2 with h | h
    · omega
    · apply coord_min f hf xstar i
      intro t
      convert h.2 i hi i (xstar i + t) using 1
      congr 1
      ext j
      simp [PiLp.single_apply]
      split_ifs <;> simp_all <;> ring
