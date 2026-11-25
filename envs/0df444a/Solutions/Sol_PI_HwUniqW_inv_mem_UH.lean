-- Prove2me | solution 1 for PI.HwUniqW.inv_mem_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:29.699057+00:00
-- url     : https://prove2.me/submissions/8bbcc3c1-6d7a-4741-8558-0dbc532f38f9

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Theorems.Thm_PI_HwUniqW_Hpk_mul_self
import Theorems.Thm_PI_HwUniqW_Hpk_conjTranspose
import Theorems.Thm_PI_HwUniqW_inv_eq_UH
import Theorems.Thm_PI_HwUniqW_mul_inv_UH

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
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
namespace PI.HwUniqW
theorem _root_.solution {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  have hh : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Hpk k r * (Hpk k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Hpk_mul_self, Matrix.one_mul]
  have h1 : a * (Hpk k r * aᴴ * Hpk k r) = 1 := by
    rw [← inv_eq_UH ha]
    exact mul_inv_UH ha
  have h2 : a * Hpk k r * aᴴ = Hpk k r := by
    calc a * Hpk k r * aᴴ = a * (Hpk k r * aᴴ * Hpk k r) * Hpk k r := by
          simp only [Matrix.mul_assoc, Hpk_mul_self, Matrix.mul_one]
      _ = Hpk k r := by rw [h1, Matrix.one_mul]
  have e : (a⁻¹)ᴴ = Hpk k r * a * Hpk k r := by
    rw [inv_eq_UH ha]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_conjTranspose,
      Matrix.mul_assoc]
  rw [e, inv_eq_UH ha]
  calc Hpk k r * a * Hpk k r * Hpk k r * (Hpk k r * aᴴ * Hpk k r)
      = Hpk k r * (a * Hpk k r * aᴴ) * Hpk k r := by simp only [Matrix.mul_assoc, hh]
    _ = Hpk k r := by rw [h2, Hpk_mul_self, Matrix.one_mul]
end PI.HwUniqW
