-- Prove2me | solution 1 for TunnellMap.BlockGen.advance_eq_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:31:46.52417+00:00
-- url     : https://prove2.me/submissions/f6cc3d0d-55c1-4dfe-95d4-7db4cb47fa94

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState

set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} (h : advance s F st = none) :
    remainingTrace s F st = [] :=
  (advance_step F st).2 h
end TunnellMap.BlockGen
