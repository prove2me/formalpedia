-- Prove2me | solution 1 for PI.StabPairsW.gramM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:54:01.795613+00:00
-- url     : https://prove2.me/submissions/e74fe2d0-7cec-49f8-9c04-72c79f532db8

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
    gramM k r z z' γ = (Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ := by
  ext i j
  rw [conjTranspose_mul_mul_apply_eq_dotProduct]
  rfl
end PI.StabPairsW
