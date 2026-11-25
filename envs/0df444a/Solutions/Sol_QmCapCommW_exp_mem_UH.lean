-- Prove2me | solution 1 for QmCapCommW.exp_mem_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:52.946656+00:00
-- url     : https://prove2.me/submissions/7f3fd7d4-e0ee-46cc-836d-1cccb4d61d06

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_CapelliOperatorCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open QmCapCommW
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace QmCapCommW
theorem _root_.solution {n : ℕ} (H Y : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ UH H := by
  have hU : IsUnit H := IsUnit.of_mul_eq_one _ hH
  have hinv : H⁻¹ = H := Matrix.inv_eq_left_inv hH
  have h1 : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
    rw [hinv]
    calc Yᴴ = Yᴴ * H * H := by rw [Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = H * (-Y) * H := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hU, hinv]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH, Matrix.mul_one, Matrix.mul_assoc, hc,
    Matrix.mul_one]
end QmCapCommW
