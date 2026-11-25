-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_top_c3fbe0f74289
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:36.97613+00:00
-- url     : https://prove2.me/submissions/b20f5f84-61ad-4046-ba4d-e129b8d12360

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_6d540496c75a

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
theorem _root_.solution (N : ℕ) (t : ℤ) (ht : (N : ℤ) ≤ t) :
    diff1^[N] (projSpaceHilb N) t = 1 := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + N := ⟨(t - N).toNat, by omega⟩
  rw [iter_projSpaceHilb N N le_rfl s, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
end GroundTheory.Heights₂.Heights.FieldNumbers
