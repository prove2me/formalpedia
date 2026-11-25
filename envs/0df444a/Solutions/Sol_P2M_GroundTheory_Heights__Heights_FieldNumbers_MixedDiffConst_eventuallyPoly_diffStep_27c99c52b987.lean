-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_diffStep_27c99c52b987
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:32.371869+00:00
-- url     : https://prove2.me/submissions/cb589bf7-f1e0-4ca7-950d-8d6503eccd85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMixedDiffConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eval_shiftPoly_461cf4c54608

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
theorem _root_.solution (b : K → ℤ) {g : (K → ℤ) → ℤ} {q : MvPolynomial K ℚ}
    (hq : EventuallyPoly g q) : EventuallyPoly (diffStep b g) (polyStep b q) := by
  have ht : Tendsto (fun m : K → ℤ => m - b) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-b) tendsto_id
  filter_upwards [hq, ht.eventually hq] with m h1 h2
  simp only [diffStep, polyStep, map_sub, eval_shiftPoly]
  rw [Int.cast_sub, h1, h2]
  simp [Pi.sub_apply]
end GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
