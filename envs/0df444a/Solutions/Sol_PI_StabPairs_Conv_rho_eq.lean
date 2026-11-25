-- Prove2me | solution 1 for PI.StabPairs.Conv.rho_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:22.819142+00:00
-- url     : https://prove2.me/submissions/8772d622-f848-4a90-9b3b-d1a173b627ee

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec

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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
namespace PI.StabPairs.Conv
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    PI.StabPairsW.rhoOf k r z z' γ u u' =
      PI.StabPairs.ConvAlg.rhoOf (Hpk k r) (Fm k r z z' γ) (Wm u u') := by
  have hG : gramM k r z z' γ = (Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ := by
    ext i j
    simp only [gramM, herm, Fm, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Matrix.conjTranspose_apply, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  unfold PI.StabPairsW.rhoOf PI.StabPairs.ConvAlg.rhoOf PI.StabPairsW.Km
  rw [hG]
  simp only [Matrix.mul_assoc]
end PI.StabPairs.Conv
