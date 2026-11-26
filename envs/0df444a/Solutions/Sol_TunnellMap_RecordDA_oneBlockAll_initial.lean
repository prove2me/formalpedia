-- Prove2me | solution 1 for TunnellMap.RecordDA.oneBlockAll_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:50:09.899821+00:00
-- url     : https://prove2.me/submissions/28f1a69b-0b30-40df-bb6c-e9a13333e90b

import Definitions.Def_TunnellMap_BlockGeneratorState
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Theorems.Thm_TunnellMap_BlockGen_oneBlock_initial


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
variable {frames : FrameFamily n} {E : DARun n} {s old : BResidual n}
  {rest : List (BResidual n)} {r rold : IncidentRecord} {g : GenState}
namespace TunnellMap.RecordDA
theorem _root_.solution (frames : FrameFamily n)
    (sources : List (BResidual n)) :
    OneBlockAll frames (DARun.initial sources) :=
  fun s => oneBlock_initial (frames s)
end TunnellMap.RecordDA
