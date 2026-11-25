-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_prod_norm_embeddings_9bcca348aca7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:38:40.006576+00:00
-- url     : https://prove2.me/submissions/bd5817e6-4de3-451e-9c5a-41be4d6e000a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup

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
theorem _root_.solution (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have h : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = ∏ σ : K →+* ℂ, ‖σ x‖ := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x, norm_prod, ← Fintype.prod_equiv
      (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖) (fun φ => ‖φ x‖)
      fun _ => by simp [RingHom.equivRatAlgHom_apply]]
  rw [← h, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, Rat.cast_abs]
end GroundTheory.Heights₂.Heights
