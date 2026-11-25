-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_none_b7c995227689
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:58.117238+00:00
-- url     : https://prove2.me/submissions/138fb64e-5f59-43e8-9da2-ea8ed0219acb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct

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
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (c : K → ℤ) : pullDeg Function.Embedding.some c none = 0 := by
  unfold pullDeg
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨a, h⟩
    exact Option.some_ne_none a h
end GroundTheory.Heights₂.Heights.FieldNumbers
