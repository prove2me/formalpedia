-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_unitChart_e84cbb7a7312
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:53.853945+00:00
-- url     : https://prove2.me/submissions/e6024929-14c6-4855-a7d1-a4bde164aff4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_continuous_evalCone_7b41833d48e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial_ne_zero_cbad317c02fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_isCompact_unitChart_862e6b4bfb8b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (e : MvPolynomial (Coord n) ℤ) : ∃ B : ℝ, ∀ z ∈ unitChart c, chartNorm A c d e z ≤ B := by
  have hnz : ∀ z ∈ unitChart c, BlockNonzero z := fun z hz k h0 ↦ by
    have := hz.1 k
    rw [h0] at this
    exact zero_ne_one this
  have hcont : ContinuousOn (chartNorm A c d e) (unitChart c) := by
    refine ContinuousOn.div (continuous_evalCone e).norm.continuousOn
      (((continuous_evalCone _).norm.continuousOn).mul
        (A.metric_smooth.continuousOn.mono fun z hz ↦ hnz z hz)) fun z hz ↦ ?_
    refine mul_ne_zero (norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d fun k ↦ ?_))
      (A.metric_pos z (hnz z hz)).ne'
    rw [hz.1 k]
    exact one_ne_zero
  obtain ⟨B, hB⟩ := (isCompact_unitChart c).exists_bound_of_continuousOn hcont
  exact ⟨B, fun z hz ↦ (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z hz))⟩
end GroundTheory.Heights₂.Heights.BoundedMonomials
