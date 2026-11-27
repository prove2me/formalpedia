-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceLelongError_proof_a0b3c62d8b86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:39.125898+00:00
-- url     : https://prove2.me/submissions/186bc6f1-ad1c-4f50-8fb8-2614368ade1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLelongError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceWeightBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBandEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLelongError
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_deriv_smoothTransition_eq_zero_da03c9a154fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_continuous_derivs_d2f475853b26
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_exists_bound_derivs_a1c87390a494
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_bound_aux_73e60d2943e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_continuous_dualNorm_d0655469d688
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_measurable_f92e47842fbb


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
open MvPolynomial Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.SliceLelongError
namespace GroundTheory.Heights₂.Heights.SliceLelongError
theorem _root_.solution (h₁ : SliceCutChain.Statement) (h₂ : SliceWeightBound.Statement)
    (h₃ : SliceBandEnergy.Statement) : SliceLelongError.Statement := by
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨M₁, M₂, hM₁, hM₂⟩ := exists_bound_derivs
  obtain ⟨C₂, hC₂⟩ := h₂ n e h J F u ℓ hJ hF hu hℓ
  obtain ⟨C₃, hC₃⟩ := h₃ n e h J F u ℓ hJ hF hu hℓ hℓW
  have hL : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x) :=
    Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable
  refine squeeze_zero_norm (a := fun k : ℕ => (|C₂ * M₁| + 2 * |C₃ * M₂|) / ((k : ℝ) + 1))
    (fun k => ?_) (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hw : Measurable fun x : Fin n → ℂ => 2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1) :=
    measurable_const.sub (hL.div_const _)
  have e1 := hC₂ (fun x => deriv Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))) M₁
    (continuous_derivs.1.measurable.comp hw) fun x => hM₁ _
  have e2 := hC₃
    (fun x => deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))) M₂
    ((k : ℝ) + 1) (2 * ((k : ℝ) + 1)) (continuous_derivs.2.measurable.comp hw) (fun x => hM₂ _)
    (by linarith) fun x hx => by
      by_contra hb
      rw [not_and_or, not_le, not_le] at hb
      refine hx (deriv_smoothTransition_eq_zero ?_).2
      rcases hb with hb | hb
      · have : Real.log (h.dualNorm x) / ((k : ℝ) + 1) < 1 := (div_lt_one hk).mpr hb
        right; linarith
      · have : 2 < Real.log (h.dualNorm x) / ((k : ℝ) + 1) := (lt_div_iff₀ hk).mpr hb
        left; linarith
  rw [Real.norm_eq_abs, h₁ n e h J F u ℓ k hJ hF hu hℓ]
  exact bound_aux (Nat.cast_nonneg k) e1 e2
end GroundTheory.Heights₂.Heights.SliceLelongError
