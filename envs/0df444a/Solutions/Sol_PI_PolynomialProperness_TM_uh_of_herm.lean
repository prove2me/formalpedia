-- Prove2me | solution 1 for PI.PolynomialProperness.TM.uh_of_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:16.332698+00:00
-- url     : https://prove2.me/submissions/5cead90a-736e-49ca-82ea-d407eb17fcc1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.TM
namespace PI.PolynomialProperness.TM
theorem _root_.solution {m : ℕ} {H g : Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ x y : Fin m → ℂ, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) : g ∈ UH H := by
  show gᴴ * H * g = H
  have hg : ∀ v w : Fin m → ℂ, herm H (g *ᵥ v) (g *ᵥ w) = herm (gᴴ * H * g) v w := by
    intro v w
    unfold herm
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have e1 : ∀ (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m),
      herm M (Pi.single j 1) (Pi.single i 1) = M i j := by
    intro M i j
    have hs : star (Pi.single i 1 : Fin m → ℂ) = (Pi.single i 1 : Fin m → ℂ) := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp
      · simp [Pi.single_apply, hk]
    unfold herm
    rw [hs]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ext i j
  have h1 := h (Pi.single j 1) (Pi.single i 1)
  rw [hg, e1, e1] at h1
  exact h1
end PI.PolynomialProperness.TM
