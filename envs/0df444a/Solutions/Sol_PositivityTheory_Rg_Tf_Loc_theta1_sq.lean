-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.theta1_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:09.792625+00:00
-- url     : https://prove2.me/submissions/5e05998b-3b75-4f5b-ba3e-1cc9abba02dc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_one
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_pow
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_thetaGL_apply
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_invTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_invTransposeGL_invTransposeGL

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
theorem _root_.solution (σ : E ≃ₐ[k] E) (hσ : σ ^ 2 = 1) :
    (theta1 σ : Monoid.End (GL n E)) ^ 2 = 1 := by
  have hθ : ∀ g : GL n E, theta1 σ g = invTransposeGL (sigmaGL σ g) := fun g => by
    rw [theta1, thetaGL_apply, one_mul, inv_one, mul_one]
  have h2 : (sigmaGL σ : Monoid.End (GL n E)) ^ 2 = 1 := by
    rw [← sigmaGL_pow, hσ, sigmaGL_one]
  have hσσ : ∀ g : GL n E, sigmaGL σ (sigmaGL σ g) = g := fun g => by
    show (sigmaGL σ * sigmaGL σ : Monoid.End (GL n E)) g = g
    rw [← pow_two, h2]
    rfl
  refine MonoidHom.ext fun g => ?_
  rw [pow_two]
  show theta1 σ (theta1 σ g) = g
  rw [hθ, hθ, sigmaGL_invTransposeGL, invTransposeGL_invTransposeGL, hσσ]
end PositivityTheory.Rg.Tf.Loc
