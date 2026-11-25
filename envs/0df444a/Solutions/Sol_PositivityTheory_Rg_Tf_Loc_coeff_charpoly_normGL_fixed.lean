-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.coeff_charpoly_normGL_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:26.315852+00:00
-- url     : https://prove2.me/submissions/db751d66-4701-4a0a-b6cb-8206e4f4b27c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_charpoly_twNorm_map

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
theorem _root_.solution (σ : E ≃ₐ[k] E) (hℓ : σ ^ Module.finrank k E = 1)
    (δ : GL n E) (i : ℕ) :
    σ (((normGL σ δ : GL n E) : Matrix n n E).charpoly.coeff i) =
      ((normGL σ δ : GL n E) : Matrix n n E).charpoly.coeff i := by
  have h := congrArg (fun p => Polynomial.coeff p i) (charpoly_twNorm_map σ hℓ δ)
  simpa [normGL, Polynomial.coeff_map] using h
end PositivityTheory.Rg.Tf.Loc
