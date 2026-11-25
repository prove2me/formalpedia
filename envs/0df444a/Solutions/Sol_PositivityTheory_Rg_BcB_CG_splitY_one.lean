-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.splitY_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:36:56.276337+00:00
-- url     : https://prove2.me/submissions/f69f9153-7201-48f3-9950-a8c82b904531

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
theorem _root_.solution [One X] (w : ι) : splitY w (1 : X) (1 : {v // v ≠ w} → X) = 1 := by
  funext v
  by_cases h : v = w <;> simp [splitY, h]
end PositivityTheory.Rg.BcB.CG
