-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.sigmaGL_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:04.583075+00:00
-- url     : https://prove2.me/submissions/543214b9-08ef-46a6-a200-9150f7208831

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
theorem _root_.solution (τ : E ≃ₐ[k] E) (g : GL n E) :
    ((sigmaGL τ g : GL n E) : Matrix n n E) = (g : Matrix n n E).map τ := rfl
end PositivityTheory.Rg.Tf.Loc
