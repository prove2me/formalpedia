-- Prove2me | solution 1 for ZetaZeros.D.EllReg.weightedNormFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:16.737811+00:00
-- url     : https://prove2.me/submissions/61c374f2-6a12-41a9-a042-41f7c159a583

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_BaseLevel
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightedNormFinite
import Theorems.Thm_ZetaZeros_D_EllReg_om_nonneg
import Theorems.Thm_ZetaZeros_D_EllReg_om_sq_le
import Theorems.Thm_ZetaZeros_D_EllReg_norm_fourier_le_integral_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
namespace ZetaZeros.D.EllReg
theorem _root_.solution : FiniteWeighted := by
  unfold FiniteWeighted
  intro d g hg hgc s M ε hε hsM
  unfold nrm
  have hint0 : Integrable (fun ξ : E d => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 * (M - s)) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [finrank_euclideanSpace_fin]
    linarith
  have hexp : -(2 * (M - s)) / 2 = s - M := by ring
  rw [hexp] at hint0
  have hint_r := (hint0.const_mul (max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)))).mul_const
    ((∫ x, ‖g x‖) ^ 2)
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hint_r.lintegral_lt_top
  have hK : 0 ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) :=
    le_max_of_le_right (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  have hw := om_nonneg s M ε ξ
  have hreal : om s M ε ξ ^ 2 * ‖𝓕 g ξ‖ ^ 2 ≤
      max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + ‖ξ‖ ^ 2) ^ (s - M) *
        (∫ x, ‖g x‖) ^ 2 := by
    refine mul_le_mul (om_sq_le s M ε hε ξ) ?_ (sq_nonneg _)
      (mul_nonneg hK (Real.rpow_nonneg (by positivity) _))
    rw [sq, sq]
    exact mul_self_le_mul_self (norm_nonneg _) (norm_fourier_le_integral_norm g ξ)
  have heq : ENNReal.ofReal (om s M ε ξ) ^ 2 * ‖𝓕 g ξ‖ₑ ^ 2 =
      ENNReal.ofReal (om s M ε ξ ^ 2 * ‖𝓕 g ξ‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow hw, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]
  exact heq.trans_le (ENNReal.ofReal_le_ofReal hreal)
end ZetaZeros.D.EllReg
