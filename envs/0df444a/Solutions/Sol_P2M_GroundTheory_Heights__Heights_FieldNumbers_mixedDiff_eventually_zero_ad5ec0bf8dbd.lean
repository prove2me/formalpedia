-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_eventually_zero_ad5ec0bf8dbd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:27.547336+00:00
-- url     : https://prove2.me/submissions/f5b817ac-9dd4-4067-8da2-4dcd3823260d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumZeroSlot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_eventually_zero_4956435bfa67

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
open GroundTheory.Heights₂.Heights.NumbersDVR Filter
universe u
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {n : ℕ} (bs : Fin n → K → ℤ) {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, mixedDiff bs h m = 0 := by
  unfold mixedDiff
  induction List.ofFn bs with
  | nil => simpa using hh
  | cons a t ih => exact diffStep_eventually_zero ih
end GroundTheory.Heights₂.Heights.FieldNumbers
