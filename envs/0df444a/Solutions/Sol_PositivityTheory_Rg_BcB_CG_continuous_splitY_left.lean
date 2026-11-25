-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.continuous_splitY_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:11.703924+00:00
-- url     : https://prove2.me/submissions/bf492a99-473b-4e6c-b377-ded61865d234

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
theorem _root_.solution [TopologicalSpace X] (w : ι) (z : {v // v ≠ w} → X) :
    Continuous fun t : X => splitY w t z :=
  continuous_pi fun v => by
    by_cases h : v = w
    · simp only [splitY, dif_pos h]; exact continuous_id
    · simp only [splitY, dif_neg h]; exact continuous_const
end PositivityTheory.Rg.BcB.CG
