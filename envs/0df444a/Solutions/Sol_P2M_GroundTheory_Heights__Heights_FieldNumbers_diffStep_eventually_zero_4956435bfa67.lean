-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_eventually_zero_4956435bfa67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:53:29.308353+00:00
-- url     : https://prove2.me/submissions/3a509336-a3bf-43a6-b83a-066196acd075

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumZeroSlot

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
theorem _root_.solution {b : K → ℤ} {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, diffStep b h m = 0 := by
  have hs : ∀ᶠ m in atTop, h (m + -b) = 0 :=
    (tendsto_atTop_add_const_right atTop (-b) tendsto_id).eventually hh
  filter_upwards [hh, hs] with m h1 h2
  simp only [diffStep, h1, ← sub_eq_add_neg] at h2 ⊢
  rw [h2, sub_zero]
end GroundTheory.Heights₂.Heights.FieldNumbers
