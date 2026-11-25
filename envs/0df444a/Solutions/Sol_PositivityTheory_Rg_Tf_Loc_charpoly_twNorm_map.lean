-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.charpoly_twNorm_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:49.123302+00:00
-- url     : https://prove2.me/submissions/1d218dab-f0f9-40bf-8da1-f488adceb0f5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_map_twNorm_of_pow_eq_one
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_one
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_pow

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
theorem _root_.solution (σ : E ≃ₐ[k] E) {ℓ : ℕ} (hℓ : σ ^ ℓ = 1) (δ : GL n E) :
    ((twNorm (sigmaGL σ) ℓ δ : GL n E) : Matrix n n E).charpoly.map (σ.toAlgHom.toRingHom) =
      ((twNorm (sigmaGL σ) ℓ δ : GL n E) : Matrix n n E).charpoly := by
  have hθ : (sigmaGL σ : Monoid.End (GL n E)) ^ ℓ = 1 := by rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  rw [← Matrix.charpoly_map]
  have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hθ δ
  have h2 : ((twNorm (sigmaGL σ) ℓ δ : GL n E) : Matrix n n E).map σ.toAlgHom.toRingHom =
      ((sigmaGL σ (twNorm (sigmaGL σ) ℓ δ) : GL n E) : Matrix n n E) := rfl
  rw [h2, h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
end PositivityTheory.Rg.Tf.Loc
