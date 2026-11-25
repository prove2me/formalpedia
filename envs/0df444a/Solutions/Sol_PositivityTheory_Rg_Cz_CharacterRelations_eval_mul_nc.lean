-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.eval_mul_nc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:08.994798+00:00
-- url     : https://prove2.me/submissions/7839bfc5-a5d6-4a89-94be-ddbcbc65d4f7

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
theorem _root_.solution (p q : A[X]) (x : A) (h : ∀ k, Commute (q.coeff k) x) :
    (p * q).eval x = p.eval x * q.eval x := by
  exact Polynomial.eval₂_mul_noncomm (RingHom.id A) x h
end PositivityTheory.Rg.Cz.CharacterRelations
