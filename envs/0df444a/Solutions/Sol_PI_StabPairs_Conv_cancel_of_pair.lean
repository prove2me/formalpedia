-- Prove2me | solution 1 for PI.StabPairs.Conv.cancel_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:36.4988+00:00
-- url     : https://prove2.me/submissions/71660af6-175d-403c-ad9b-52823593a394

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Theorems.Thm_PI_StabPairs_Conv_ut_det
import Theorems.Thm_PI_StabPairs_Conv_ut_conj_fix

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
theorem _root_.solution {r : ℕ} {u u' Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (hZ : IsUnit Z.det) (hp : uᴴ * Z * u' = Z) (c : Fin (r + 1) → ℂ)
    (hc : ∀ a : Fin (r + 1), a.val < r → (Z *ᵥ c) a = 0) : (u' - 1) *ᵥ c = 0 := by
  have hA : IsUnit (uᴴ * Z).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, ut_det hu, star_one, one_mul]; exact hZ
  have h0 : (uᴴ * Z) *ᵥ ((u' - 1) *ᵥ c) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hp, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, ut_conj_fix hu _ hc, sub_self]
  calc (u' - 1) *ᵥ c = ((uᴴ * Z)⁻¹ * (uᴴ * Z)) *ᵥ ((u' - 1) *ᵥ c) := by
        rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
end PI.StabPairs.Conv
