-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chowHeightConst_8b6933d50429
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:20:30.694922+00:00
-- url     : https://prove2.me/submissions/16e6890f-f8ae-487c-9ec9-6d2171b389db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahler_C_02c18ff6a9ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_log_norm_embeddings_2fdebfa8404c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_adicAbv_f04fbb456bfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_C_3de71e041495


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
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : ChowHeightConst.Statement := by
  intro K _ _ n k H c hc
  unfold chowHt
  have harch : ∀ σ : K →+* ℂ,
      mahler (H.normAt σ) k ((C c : MvPolynomial (Fin k × Fin n) K).map σ) = Real.log ‖σ c‖ :=
    fun σ => by rw [map_C, mahler_C]
  simp only [harch, gaussNorm_C, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero,
    finsum_log_adicAbv hc, sum_log_norm_embeddings hc, neg_add_cancel]
end GroundTheory.Heights₂.Heights
