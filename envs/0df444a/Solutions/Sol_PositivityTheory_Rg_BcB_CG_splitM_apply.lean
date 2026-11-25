-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.splitM_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:32:41.082047+00:00
-- url     : https://prove2.me/submissions/0c952447-1ff9-4abc-9fb7-f212d9d7b6f2

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
variable {Idx : ι → Type}
namespace PositivityTheory.Rg.BcB.CG
theorem _root_.solution [MeasurableSpace X] (w : ι) (y : ι → X) : splitM w y = (y w, fun v : {v // v ≠ w} => y v) := rfl
end PositivityTheory.Rg.BcB.CG
