-- Prove2me | solution 1 for TunnellMap.BlockGen.drain_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:37.147572+00:00
-- url     : https://prove2.me/submissions/38c65b81-5d74-4d0b-96ce-4bda814200a4

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState
import Theorems.Thm_TunnellMap_BlockGen_drain_eq_remainingTrace
import Theorems.Thm_TunnellMap_BlockGen_remainingTrace_initial
attribute [local simp] TunnellMap.BlockGen.remainingTrace_initial



set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (F : OrthogonalFrame (tau (residualSourceLift s))) :
    drain s F GenState.initial = fullTrace s F := by
  rw [drain_eq_remainingTrace, remainingTrace_initial]
end TunnellMap.BlockGen
