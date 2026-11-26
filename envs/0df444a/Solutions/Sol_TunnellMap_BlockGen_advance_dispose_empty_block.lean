-- Prove2me | solution 1 for TunnellMap.BlockGen.advance_dispose_empty_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:25:30.973884+00:00
-- url     : https://prove2.me/submissions/e3fd0629-d40d-443a-b2c8-3f932b2d9d16

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState
import Theorems.Thm_TunnellMap_BlockGen_advance_nil_of_le

set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (F : OrthogonalFrame (tau (residualSourceLift s)))
    {h : ℤ} (hle : h ≤ hMax n) (hb : blockRecords s F h = []) :
    advance s F ⟨h, []⟩ = advance s F ⟨h + 1, []⟩ := by
  rw [advance_nil_of_le F hle, hb]
end TunnellMap.BlockGen
