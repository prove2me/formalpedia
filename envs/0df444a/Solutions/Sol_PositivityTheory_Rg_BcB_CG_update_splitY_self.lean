-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.update_splitY_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:28:46.741275+00:00
-- url     : https://prove2.me/submissions/bbf37ff4-2fb2-4feb-9256-7a924537c98f

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
theorem _root_.solution (w : ι) (t t' : X) (z : {v // v ≠ w} → X) :
    Function.update (splitY w t z) w t' = splitY w t' z := by
  funext v
  simp only [Function.update_apply, splitY]
  by_cases h : v = w
  · rw [if_pos h, dif_pos h]
  · rw [if_neg h]; simp [h]
end PositivityTheory.Rg.BcB.CG
