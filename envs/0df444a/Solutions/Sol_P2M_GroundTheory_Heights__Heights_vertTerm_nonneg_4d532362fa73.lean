-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_vertTerm_nonneg_4d532362fa73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:06.704747+00:00
-- url     : https://prove2.me/submissions/99534235-566d-4643-aee6-606ed2fedeaf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional

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
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) (u : Fin n → 𝓞 K) :
    0 ≤ vertTerm I k u := by
  unfold vertTerm vertTermAt
  refine finsum_nonneg fun v => finsum_nonneg fun W => finsum_nonneg fun _ => ?_
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_natCast_nonneg _)
end GroundTheory.Heights₂.Heights
