-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sum_log_norm_embeddings_2fdebfa8404c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:46.284873+00:00
-- url     : https://prove2.me/submissions/40df2c36-1689-4060-a23b-05d7a0501030

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_prod_norm_embeddings_9bcca348aca7

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
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ x‖ = Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  rw [← prod_norm_embeddings, Real.log_prod]
  intro σ _
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx)
end GroundTheory.Heights₂.Heights
