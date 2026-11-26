-- Prove2me | solution 1 for TunnellMap.BlockGen.advance_nil_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:22.804952+00:00
-- url     : https://prove2.me/submissions/e883b068-7610-4955-b598-f7a5870c1350

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState

set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (F : OrthogonalFrame (tau (residualSourceLift s)))
    {h : ℤ} (hle : h ≤ hMax n) :
    advance s F ⟨h, []⟩ = advance s F ⟨h + 1, blockRecords s F h⟩ := by
  rw [advance, if_pos hle]
end TunnellMap.BlockGen
