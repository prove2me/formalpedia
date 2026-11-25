-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.update_splitY_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:21.980901+00:00
-- url     : https://prove2.me/submissions/36503cf4-ee0a-43e0-95f3-ec2996149c3a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG
variable {ι : Type} [DecidableEq ι] {X : Type}
namespace PositivityTheory.Rg.BcB.CG
theorem _root_.solution (w : ι) (t : X) (z : {v // v ≠ w} → X) (v : {v // v ≠ w}) (s : X) :
    Function.update (splitY w t z) v s = splitY w t (Function.update z v s) := by
  funext x
  simp only [Function.update_apply, splitY]
  by_cases h : x = w
  · have h' : x ≠ (v : ι) := fun e => v.2 (e ▸ h)
    rw [if_neg h', dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    by_cases h' : x = v
    · have : (⟨x, h⟩ : {v // v ≠ w}) = v := Subtype.ext h'
      rw [if_pos h', if_pos this]
    · have : (⟨x, h⟩ : {v // v ≠ w}) ≠ v := fun e => h' (congrArg Subtype.val e)
      rw [if_neg h', if_neg this]
end PositivityTheory.Rg.BcB.CG
