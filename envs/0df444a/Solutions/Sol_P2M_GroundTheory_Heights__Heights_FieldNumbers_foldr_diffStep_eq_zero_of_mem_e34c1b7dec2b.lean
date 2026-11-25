-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_eq_zero_of_mem_e34c1b7dec2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:27:55.034797+00:00
-- url     : https://prove2.me/submissions/d77c9497-a395-4ca8-9fa4-d4148050be80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumZeroSlot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_zero_left_a8b289153ceb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_zero_right_5689229da9c5

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
theorem _root_.solution (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l)
    (h : (K → ℤ) → ℤ) : l.foldr diffStep h = 0 := by
  induction l with
  | nil => simp at hl
  | cons a t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hl with rfl | ht
    · exact diffStep_zero_left _
    · rw [ih ht]
      exact diffStep_zero_right a
end GroundTheory.Heights₂.Heights.FieldNumbers
