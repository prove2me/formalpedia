-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.prod_neg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:12.04084+00:00
-- url     : https://prove2.me/submissions/f15cd711-25cc-4f16-bd51-91b589a7b039

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar

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
open PositivityTheory.Rg.Cz.CharacterRelations
variable {A : Type*} [Ring A] [Algebra ℂ A]
set_option linter.unusedSectionVars false
namespace PositivityTheory.Rg.Cz.CharacterRelations
theorem _root_.solution (L : List A) (h : (L.map fun x => -x).prod = 0) : L.prod = 0 := by
  rw [List.prod_map_neg] at h
  have hu : IsUnit ((-1 : A) ^ L.length) := (isUnit_one.neg).pow _
  exact hu.mul_right_eq_zero.1 h
end PositivityTheory.Rg.Cz.CharacterRelations
