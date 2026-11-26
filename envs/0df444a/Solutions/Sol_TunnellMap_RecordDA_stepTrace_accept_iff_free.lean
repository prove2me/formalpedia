-- Prove2me | solution 1 for TunnellMap.RecordDA.stepTrace_accept_iff_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:33:15.596567+00:00
-- url     : https://prove2.me/submissions/586ac913-b450-423b-b38f-adaefafc51d3

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
import Theorems.Thm_TunnellMap_RecordDA_stepTrace_shape

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution (frames : FrameFamily n) {E : DARun n}
    {ev : DAEvent n} {E' : DARun n} (h : stepTrace frames E = some (ev, E')) :
    ev.outcome = DAOutcome.accept ↔ E.held ev.target = none :=
  (stepTrace_shape frames h).choose_spec.choose_spec.choose_spec.2.2.2.2.2
end TunnellMap.RecordDA
