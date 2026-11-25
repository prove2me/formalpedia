-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.stepChar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:57.17881+00:00
-- url     : https://prove2.me/submissions/a8ff33f6-873c-43d4-b0be-1e02b360df56

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_part1
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_part2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → StepFormula → QdetFacts → StepChar := by
  intro hT hS hQ n M _ _ E hE l hl
  refine ⟨CharacterRelations.part1 hT hS hQ E hE l hl, ?_⟩
  intro W N _ _ F q hW hO k hq hqF hqO
  exact CharacterRelations.part2 hT hS hQ E hE l hl W N F q hW hO k hq hqF hqO
end PositivityTheory.Rg.Cz
