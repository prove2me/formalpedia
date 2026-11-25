-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_eq_zero_of_eventually_const_cf126017d8d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:43.891909+00:00
-- url     : https://prove2.me/submissions/a131f3f8-c483-47c9-b2f6-cde77d210ea1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_apply_0b5964759951

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {g : ℤ → ℤ} {a c : ℤ} (h : ∀ s : ℕ, g (s + a) = c) (s : ℕ) :
    diff1 g (s + (a + 1)) = 0 := by
  rw [backwardDifference_apply, show (s : ℤ) + (a + 1) = ((s + 1 : ℕ) : ℤ) + a by push_cast; ring,
    show ((s + 1 : ℕ) : ℤ) + a - 1 = (s : ℤ) + a by push_cast; ring, h, h, sub_self]
end GroundTheory.Heights₂.Heights.FieldNumbers
