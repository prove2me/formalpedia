-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.thetaGL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:43:44.668433+00:00
-- url     : https://prove2.me/submissions/51d6d65a-1ddc-46a1-8d06-7cf4f3c6e0e5

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
theorem _root_.solution (σ : E ≃ₐ[k] E) (J g : GL n E) :
    thetaGL σ J g = J * invTransposeGL (sigmaGL σ g) * J⁻¹ := rfl
end PositivityTheory.Rg.Tf.Loc
