-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.comm_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:50.795987+00:00
-- url     : https://prove2.me/submissions/3fe1fbf1-93de-409b-8040-2f42e22bed16

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
theorem _root_.solution (y : A) (u : ℂ) : Commute y (algebraMap ℂ A u) := (Algebra.commutes u y).symm
end PositivityTheory.Rg.Cz.CharacterRelations
