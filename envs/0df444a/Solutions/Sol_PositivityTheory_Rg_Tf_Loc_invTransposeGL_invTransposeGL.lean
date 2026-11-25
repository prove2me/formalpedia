-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.invTransposeGL_invTransposeGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:55.353679+00:00
-- url     : https://prove2.me/submissions/dc157af4-62b8-4995-b84b-9ea8c72e921a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Tf PositivityTheory.Rg.Tf.Loc
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k E : Type*} [Field k] [Field E] [Algebra k E]
namespace PositivityTheory.Rg.Tf.Loc
theorem _root_.solution (g : GL n E) :
    invTransposeGL (invTransposeGL g) = g :=
  Units.ext (Matrix.transpose_transpose _)
end PositivityTheory.Rg.Tf.Loc
