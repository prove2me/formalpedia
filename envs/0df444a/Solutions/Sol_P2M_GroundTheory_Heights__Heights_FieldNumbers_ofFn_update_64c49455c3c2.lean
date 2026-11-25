-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ofFn_update_64c49455c3c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:54.67227+00:00
-- url     : https://prove2.me/submissions/31d92754-7a57-42a9-8c5e-f25051f19885

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd

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
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {α : Type*} {n : ℕ} (bs : Fin n → α) (i : Fin n) (x : α) :
    List.ofFn (Function.update bs i x) = (List.ofFn bs).set i x := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff]
    split_ifs with h h' h'
    · rfl
    · exact absurd h.symm h'
    · exact absurd h'.symm h
    · rfl
end GroundTheory.Heights₂.Heights.FieldNumbers
