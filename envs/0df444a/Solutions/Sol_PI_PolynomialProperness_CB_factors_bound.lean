-- Prove2me | solution 1 for PI.PolynomialProperness.CB.factors_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:08:50.437031+00:00
-- url     : https://prove2.me/submissions/d2ddeefb-0144-4c70-a360-484314eb4f1e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
import Theorems.Thm_PI_PolynomialProperness_CB_ut_entry_bound
import Theorems.Thm_PI_PolynomialProperness_CB_lt_entry_bound
import Theorems.Thm_PI_PolynomialProperness_CB_mx_of_entry
import Theorems.Thm_PI_PolynomialProperness_CB_kap_ge
import Theorems.Thm_PI_PolynomialProperness_GN_entry_le_mx
import Theorems.Thm_PI_PolynomialProperness_GN_mx_mul_le
import Theorems.Thm_PI_PolynomialProperness_GN_mx_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB
namespace PI.PolynomialProperness.CB
theorem _root_.solution {m : ℕ} {P l u : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P.det)
    (hl : l ∈ LPg P) (hu : u ∈ UTset m) :
    (∀ i j, ‖u i j‖ ≤ Kc m P * (1 + mx (l * P * u)) ^ m) ∧
    (∀ i j, ‖l i j‖ ≤ Kc m P * (1 + mx (l * P * u)) ^ m) := by
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul _ hP
  have hPP' : P * P⁻¹ = 1 := mul_nonsing_inv _ hP
  have hX := GN.mx_nonneg (l * P * u)
  have hmP := GN.mx_nonneg P
  have hmPi := GN.mx_nonneg P⁻¹
  have hm : (0 : ℝ) ≤ m := by positivity
  have hκ := kap_ge m P
  have hA : P⁻¹ * l * P * u = P⁻¹ * (l * P * u) := by simp only [Matrix.mul_assoc]
  have hmxA : 1 + mx (P⁻¹ * l * P * u) ≤ kap m P * (1 + mx (l * P * u)) := by
    rw [hA]
    have h1 := GN.mx_mul_le P⁻¹ (l * P * u)
    unfold kap
    have : (m : ℝ) * mx P⁻¹ * mx (l * P * u) ≥ 0 := by positivity
    nlinarith
  have hA1 : 0 ≤ 1 + mx (P⁻¹ * l * P * u) := by have := GN.mx_nonneg (P⁻¹ * l * P * u); linarith
  have hpow : (1 + mx (P⁻¹ * l * P * u)) ^ m ≤ kap m P ^ m * (1 + mx (l * P * u)) ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hA1 hmxA m
  have hfac : (0 : ℝ) ≤ m.factorial := by positivity
  have hK1 : ∀ i j, ‖u i j‖ ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m ∧
      ‖(P⁻¹ * l * P) i j‖ ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m := by
    intro i j
    constructor
    · refine (ut_entry_bound hl.2 hu i j).trans ?_
      exact (mul_le_mul_of_nonneg_left hpow hfac).trans_eq (by ring)
    · refine (lt_entry_bound hl.2 hu i j).trans ?_
      exact (mul_le_mul_of_nonneg_left hpow hfac).trans_eq (by ring)
  have hY : 0 ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m := by
    have : 0 ≤ kap m P := by linarith
    positivity
  have hext : 1 ≤ 1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹ := by
    have : 0 ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ := by positivity
    linarith
  have hKeq : Kc m P * (1 + mx (l * P * u)) ^ m =
      (m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m) * (1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹) := by
    unfold Kc; ring
  constructor
  · intro i j
    rw [hKeq]
    exact (hK1 i j).1.trans (le_mul_of_one_le_right hY hext)
  · have hlt : mx (P⁻¹ * l * P) ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m :=
      mx_of_entry _ hY fun i j => (hK1 i j).2
    have hl_eq : l = P * (P⁻¹ * l * P) * P⁻¹ := by
      rw [show P * (P⁻¹ * l * P) * P⁻¹ = (P * P⁻¹) * l * (P * P⁻¹) by simp only [Matrix.mul_assoc],
        hPP', Matrix.one_mul, Matrix.mul_one]
    have hml : mx l ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ * mx (P⁻¹ * l * P) := by
      have h1 := GN.mx_mul_le (P * (P⁻¹ * l * P)) P⁻¹
      have h2 := GN.mx_mul_le P (P⁻¹ * l * P)
      rw [← hl_eq] at h1
      have := GN.mx_nonneg (P * (P⁻¹ * l * P))
      have := GN.mx_nonneg (P⁻¹ * l * P)
      calc mx l ≤ m * mx (P * (P⁻¹ * l * P)) * mx P⁻¹ := h1
        _ ≤ m * (m * mx P * mx (P⁻¹ * l * P)) * mx P⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ hmPi
            exact mul_le_mul_of_nonneg_left h2 hm
        _ = (m : ℝ) ^ 2 * mx P * mx P⁻¹ * mx (P⁻¹ * l * P) := by ring
    intro i j
    rw [hKeq]
    have hc : 0 ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ := by positivity
    calc ‖l i j‖ ≤ mx l := GN.entry_le_mx l i j
      _ ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ * mx (P⁻¹ * l * P) := hml
      _ ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ * (m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m) :=
          mul_le_mul_of_nonneg_left hlt hc
      _ ≤ (m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m) *
            (1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹) := by nlinarith
end PI.PolynomialProperness.CB
