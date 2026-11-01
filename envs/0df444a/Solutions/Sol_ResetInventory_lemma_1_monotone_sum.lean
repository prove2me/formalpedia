-- Prove2me | solution 1 for ResetInventory.lemma_1_monotone_sum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:05:12.981914+00:00
-- url     : https://prove2.me/submissions/ec03aa43-1dbc-466f-9768-f0a6a5002c93

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b M L lam : ℝ) (f f' g : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivWithinAt f (f' x) (Set.Icc a b) x)
    (_hM : 0 < M) (hf' : ∀ x ∈ Set.Icc a b, M ≤ f' x)
    (hL : 0 ≤ L) (hg : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |g x - g y| ≤ L * |x - y|)
    (hlam0 : 0 ≤ lam) (hlam : lam * L ≤ M) :
    MonotoneOn (fun x => f x + lam * g x) (Set.Icc a b) ∧
      ContinuousOn (fun x => f x + lam * g x) (Set.Icc a b) := by
  have hf_cont : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousWithinAt
  have hg_cont : ContinuousOn g (Set.Icc a b) := by
    intro x hx
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / (L + 1), div_pos hε (by linarith), fun y hy hdist => ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    have hgyx := hg y hy x hx
    have h1 : L * |y - x| ≤ (L + 1) * |y - x| := by
      nlinarith [abs_nonneg (y - x)]
    have h2 : (L + 1) * |y - x| < ε := by
      rwa [lt_div_iff₀ (by linarith), mul_comm] at hdist
    linarith
  have hsum_cont : ContinuousOn (fun x => f x + lam * g x) (Set.Icc a b) :=
    hf_cont.add (continuousOn_const.mul hg_cont)
  have h_fsub : MonotoneOn (fun x => f x - M * x) (Set.Icc a b) := by
    have hsub_deriv : ∀ x ∈ Set.Icc a b,
        HasDerivWithinAt (fun t => f t - M * t) (f' x - M) (Set.Icc a b) x := by
      intro x hx
      have hm : HasDerivWithinAt (fun t => M * t) M (Set.Icc a b) x := by
        simpa using (hasDerivWithinAt_id x (Set.Icc a b)).const_mul M
      exact (hf x hx).sub hm
    have hsub_cont : ContinuousOn (fun t => f t - M * t) (Set.Icc a b) :=
      hf_cont.sub (continuousOn_const.mul continuousOn_id)
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hsub_cont
      (fun x hx => (hsub_deriv x (interior_subset hx)).mono interior_subset) ?_
    intro x hx
    linarith [hf' x (interior_subset hx)]
  refine ⟨?_, hsum_cont⟩
  intro x hx y hy hxy
  have hfx := h_fsub hx hy hxy
  dsimp at hfx
  have hgx : |g y - g x| ≤ L * (y - x) := by
    simpa [abs_of_nonneg (sub_nonneg.mpr hxy)] using hg y hy x hx
  have hgx_low : -(L * (y - x)) ≤ g y - g x := (abs_le.mp hgx).1
  have hlam_gx : -(lam * L * (y - x)) ≤ lam * (g y - g x) := by
    nlinarith
  have hM_ge : lam * L * (y - x) ≤ M * (y - x) :=
    mul_le_mul_of_nonneg_right hlam (sub_nonneg.mpr hxy)
  linarith
