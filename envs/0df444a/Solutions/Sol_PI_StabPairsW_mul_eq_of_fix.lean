-- Prove2me | solution 1 for PI.StabPairsW.mul_eq_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:28:11.653189+00:00
-- url     : https://prove2.me/submissions/2e892041-e358-4d37-88a8-2823b6b04b7e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (γ ρ : B.Mat k r)
    (hfix : ∀ v ∈ Uperp k r z z' γ, ρ *ᵥ v = v) {ι : Type*} (Q : Matrix (Fin (2 * r + k + 1)) ι ℂ)
    (hQ : ((Fm k r z z' γ)ᴴ * Hpk k r) * Q = 0) : ρ * Q = Q := by
  have hE : (Matrix.of fun i j => star (gramVec k r z z' γ i j)) = (Fm k r z z' γ)ᴴ := by
    ext a b
    simp [Fm, Matrix.conjTranspose_apply]
  have hcol : ∀ j, (fun p => Q p j) ∈ Uperp k r z z' γ := by
    intro j
    simp only [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [hE]
    funext a
    have e := congrFun (congrFun hQ a) j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using e
  ext i j
  have e := congrFun (hfix _ (hcol j)) i
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using e
end PI.StabPairsW
