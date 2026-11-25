-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_zero_7bbe2f153d6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:21:26.678566+00:00
-- url     : https://prove2.me/submissions/9ffaefd8-bcd6-4696-a84d-192dd35269c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_maDensity_comp_affine_family_a2bd3164b5d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_of_row_zero_4634931e014b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_hermChartPot_conj_179aa3d33806
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_integral_comp_affine_bae7cf364846


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyInvariance
open ChartMongeAmpereAffineInvariance
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartEnergyInvariance
theorem _root_.solution (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (hdet : T.det ≠ 0) : EnergyInvariantUnder T := by
  intro M N hM hN k
  have ht : T 0 0 ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, zero_mul])
  have hC : (T.submatrix Fin.succ Fin.succ).det ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, mul_zero])
  set P := (T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ with hPdef
  set c : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) with hcdef
  have hP : P.det ≠ 0 := by
    rw [hPdef, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hC
  have hfM : hermChartPot (Tᴴ * M * T) = fun y => hermChartPot M (c + P *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj M T hM hT ht)
  have hfN : hermChartPot (Tᴴ * N * T) = fun y => hermChartPot N (c + P *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj N T hN hT ht)
  set Φ : Fin e → (Fin e → ℂ) → ℝ := fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ
  have hfam : (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) =
      fun j => fun y => Φ j (c + P *ᵥ y) + Real.log ‖T 0 0‖ := by
    funext j y
    by_cases h : (j : ℕ) < k <;> simp [hΦ, h, hfM, hfN]
  set f : (Fin e → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf
  have hpt : ∀ y, (hermChartPot (Tᴴ * M * T) y - hermChartPot (Tᴴ * N * T) y) *
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) y =
      Complex.normSq P.det * f (c + P *ᵥ y) := fun y => by
    rw [hfam, maDensity_comp_affine_family Φ c P hP, hfM, hfN, hf]
    ring
  unfold chartMixedEnergy
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_affine f c P hP, ← mul_assoc,
    mul_inv_cancel₀ (Complex.normSq_pos.mpr hP).ne', one_mul]
end GroundTheory.Heights₂.Heights.ChartEnergyInvariance
