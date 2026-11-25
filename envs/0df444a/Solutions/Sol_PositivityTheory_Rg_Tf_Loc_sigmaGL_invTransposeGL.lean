-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.sigmaGL_invTransposeGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:15.858834+00:00
-- url     : https://prove2.me/submissions/fa97576b-227c-4ba8-beda-e84bfc0824b9

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
    sigmaGL τ (invTransposeGL g) = invTransposeGL (sigmaGL τ g) := by
  apply Units.ext
  show (Matrix.transpose ((g⁻¹ : GL n E) : Matrix n n E)).map τ.toAlgHom.toRingHom =
    Matrix.transpose (((sigmaGL τ g)⁻¹ : GL n E) : Matrix n n E)
  rw [← map_inv]
  rfl
end PositivityTheory.Rg.Tf.Loc
