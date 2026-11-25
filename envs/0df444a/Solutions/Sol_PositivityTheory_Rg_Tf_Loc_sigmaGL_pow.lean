-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.sigmaGL_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:58.994227+00:00
-- url     : https://prove2.me/submissions/97c134f4-1f8e-4be0-bdfe-025066e005f4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_mul
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_one

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
theorem _root_.solution (τ : E ≃ₐ[k] E) (m : ℕ) :
    (sigmaGL (τ ^ m) : Monoid.End (GL n E)) = sigmaGL τ ^ m := by
  induction m with
  | zero => simpa using sigmaGL_one
  | succ m ih => rw [pow_succ, sigmaGL_mul, ih, pow_succ]
end PositivityTheory.Rg.Tf.Loc
