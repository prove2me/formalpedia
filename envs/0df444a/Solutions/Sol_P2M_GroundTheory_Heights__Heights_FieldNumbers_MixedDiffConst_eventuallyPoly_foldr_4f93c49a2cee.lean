-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_foldr_4f93c49a2cee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:15.164787+00:00
-- url     : https://prove2.me/submissions/f50cc591-87cf-4346-a0cc-984f687f1d01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMixedDiffConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_diffStep_27c99c52b987

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
theorem _root_.solution (L : List (K → ℤ)) {h : (K → ℤ) → ℤ} {p : MvPolynomial K ℚ}
    (hp : EventuallyPoly h p) : EventuallyPoly (L.foldr diffStep h) (L.foldr polyStep p) := by
  induction L with
  | nil => simpa using hp
  | cons b L ih => simpa using eventuallyPoly_diffStep b ih
end GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
