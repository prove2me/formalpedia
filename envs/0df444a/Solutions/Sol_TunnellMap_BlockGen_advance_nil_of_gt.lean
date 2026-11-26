-- Prove2me | solution 1 for TunnellMap.BlockGen.advance_nil_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:31.474636+00:00
-- url     : https://prove2.me/submissions/7311350b-2307-45d0-9f85-7f9cceec1d2f

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState

set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (F : OrthogonalFrame (tau (residualSourceLift s)))
    {h : ℤ} (hgt : ¬ h ≤ hMax n) : advance s F ⟨h, []⟩ = none := by
  rw [advance, if_neg hgt]
end TunnellMap.BlockGen
