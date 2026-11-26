-- Prove2me | solution 1 for TunnellMap.BlockGen.advance_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:15.629627+00:00
-- url     : https://prove2.me/submissions/8b506774-b1b0-4657-9a4a-ad775407ac09

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState

set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ)
    (r : IncidentRecord) (rest : List IncidentRecord) :
    advance s F ⟨h, r :: rest⟩ = some (r, ⟨h, rest⟩) := by
  rw [advance]
end TunnellMap.BlockGen
