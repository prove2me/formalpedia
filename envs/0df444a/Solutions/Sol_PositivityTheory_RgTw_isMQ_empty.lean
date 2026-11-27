-- Prove2me | solution 1 for PositivityTheory.RgTw.isMQ_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:20.456657+00:00
-- url     : https://prove2.me/submissions/e200c0a1-6e3c-409c-80f2-4983328d5bd1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsMQEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix Filter Topology MeasureTheory
open PositivityTheory PositivityTheory.RgTw
namespace PositivityTheory.RgTw
theorem _root_.solution (R : Type) [CommRing R] [Algebra ℂ R] :
    IsMQ (ι := Empty) (R := R) Empty.elim Empty.elim (fun k => if k = 0 then 1 else 0) Empty.elim := by
  refine ⟨fun k => by simp, fun k hk => ?_, fun i => i.elim⟩
  simp at hk
  simp [hk.ne']
end PositivityTheory.RgTw
