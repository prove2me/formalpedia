-- Prove2me | solution 1 for PI.StabPairsW.Zhat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:36.539408+00:00
-- url     : https://prove2.me/submissions/823cf117-9e0a-4dd0-9340-f8ff8ef97070

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
private lemma conjTranspose_mul_mul_apply_eq_dotProduct {p q : Type} [Fintype p] [Fintype q]
    (A : Matrix (Fin (2 * r + k + 1)) p ℂ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (C : Matrix (Fin (2 * r + k + 1)) q ℂ) (i : p) (j : q) :
    (Aᴴ * M * C) i j = star (fun l => A l i) ⬝ᵥ (M *ᵥ fun l => C l j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply, Pi.star_apply]
end PI.StabPairsW
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Zhat k r z z' γ = (Ff k r z)ᴴ * Hpk k r * γ * Ff k r z' := by
  ext a b
  rw [show (Ff k r z)ᴴ * Hpk k r * γ * Ff k r z' = (Ff k r z)ᴴ * Hpk k r * (γ * Ff k r z') by
    simp only [Matrix.mul_assoc], conjTranspose_mul_mul_apply_eq_dotProduct]
  have h1 : (fun l => (γ * Ff k r z') l b) = γ *ᵥ fvec k r z' b := by
    funext l
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Ff]
  rw [h1]
  rfl
end PI.StabPairsW
