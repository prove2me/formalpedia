-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_bound_metricDefect_474cdf5ff6c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:13.248579+00:00
-- url     : https://prove2.me/submissions/d64335cb-0e0e-4f58-938e-5233ff0d9deb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_metricDefect_smul_885c138dceb0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_l2Norm_de9fc54faefe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isCompact_unitSpheres_3229e8b4fb16

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (A : HermLine n) :
    ∃ M, ∀ z : Cone n ℂ, BlockNonzero z → |metricDefect A z| ≤ M := by
  have hsub : unitSpheres n ⊆ {z | BlockNonzero z} := fun z hz k h ↦ by
    have := hz k
    rw [h] at this
    simp [l2Norm] at this
  have hcont : ContinuousOn (metricDefect A) {z | BlockNonzero z} := by
    unfold metricDefect
    refine ContinuousOn.sub (A.metric_smooth.continuousOn.log fun z hz ↦ (A.metric_pos z hz).ne') ?_
    refine continuousOn_finsetSum _ fun k _ ↦ continuousOn_const.mul ?_
    exact ((continuous_l2Norm.comp (continuous_apply k)).continuousOn).log
      fun z hz ↦ (vectorL2Norm_pos (hz k)).ne'
  obtain ⟨M, hM⟩ := isCompact_unitSpheres.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨M, fun z hz ↦ ?_⟩
  let c : ι → ℂ := fun k ↦ (((l2Norm (z k))⁻¹ : ℝ) : ℂ)
  have hc : ∀ k, c k ≠ 0 := fun k ↦ by
    simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (vectorL2Norm_pos (hz k)).ne'
  have hw : (fun k i ↦ c k * z k i) ∈ unitSpheres n := by
    intro k
    change l2Norm (fun i ↦ c k * z k i) = 1
    rw [vectorL2Norm_const_mul, Complex.norm_of_nonneg (inv_nonneg.mpr (vectorL2Norm_pos (hz k)).le)]
    exact inv_mul_cancel₀ (vectorL2Norm_pos (hz k)).ne'
  have := hM _ hw
  rwa [metricDefect_smul A c z hc hz, Real.norm_eq_abs] at this
end GroundTheory.Heights₂.Heights
