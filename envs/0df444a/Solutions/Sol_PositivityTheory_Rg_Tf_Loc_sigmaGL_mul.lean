-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.sigmaGL_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:18.386992+00:00
-- url     : https://prove2.me/submissions/6b2409bd-bad2-42cb-ab7c-49ce825b1291

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
theorem _root_.solution (τ τ' : E ≃ₐ[k] E) :
    (sigmaGL (τ * τ') : Monoid.End (GL n E)) = sigmaGL τ * sigmaGL τ' := by
  ext g i j
  rfl
end PositivityTheory.Rg.Tf.Loc
