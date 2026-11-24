-- Prove2me | solution 1 for PI.StabPairsW.rho_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:29:17.999393+00:00
-- url     : https://prove2.me/submissions/d4c63e4d-1c0f-437b-8c0e-9e9f1112336f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Theorems.Thm_PI_StabPairsW_hpk_mul_self


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
theorem _root_.solution (γ : B.Mat k r) (hγ : γ ∈ B.GV k r) (ρ s0 : B.Mat k r)
    (h : ρ = γ * s0 * γ⁻¹) : γ⁻¹ * ρ * γ = s0 ∧ γ * s0 = ρ * γ := by
  have hγ' : γᴴ * Hpk k r * γ = Hpk k r := hγ
  have hl : (Hpk k r * γᴴ * Hpk k r) * γ = 1 := by
    have e : Hpk k r * (γᴴ * Hpk k r * γ) = 1 := by rw [hγ', hpk_mul_self]
    simpa only [Matrix.mul_assoc] using e
  have hinv : γ⁻¹ = Hpk k r * γᴴ * Hpk k r := Matrix.inv_eq_left_inv hl
  have h1 : γ⁻¹ * γ = 1 := by rw [hinv, hl]
  subst h
  constructor
  · calc γ⁻¹ * (γ * s0 * γ⁻¹) * γ = (γ⁻¹ * γ) * s0 * (γ⁻¹ * γ) := by
          simp only [Matrix.mul_assoc]
      _ = s0 := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  · calc γ * s0 = γ * s0 * (γ⁻¹ * γ) := by rw [h1, Matrix.mul_one]
      _ = γ * s0 * γ⁻¹ * γ := by simp only [Matrix.mul_assoc]
end PI.StabPairsW
