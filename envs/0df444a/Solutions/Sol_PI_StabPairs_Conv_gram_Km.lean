-- Prove2me | solution 1 for PI.StabPairs.Conv.gram_Km
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:49:46.094796+00:00
-- url     : https://prove2.me/submissions/d168706e-efe5-4f0b-85a1-0e24e5a64036

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
    (hGi : IsUnit (gramM k r z z' γ).det) (v : Fin (2 * r + k + 1) → ℂ) :
    gramM k r z z' γ *ᵥ (Km k r z z' γ *ᵥ v) = ((Fm k r z z' γ)ᴴ * Hpk k r) *ᵥ v := by
  unfold PI.StabPairsW.Km
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (gramM k r z z' γ)⁻¹, ← Matrix.mul_assoc (gramM k r z z' γ),
    Matrix.mul_nonsing_inv _ hGi, Matrix.one_mul]
end PI.StabPairs.Conv
