-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_chartMass_conj_47d12006171a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:07:25.960394+00:00
-- url     : https://prove2.me/submissions/4a6183c7-02ae-4f59-b815-aea184162df6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_of_row_zero_4634931e014b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_hermChartPot_conj_179aa3d33806
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_integral_comp_affine_bae7cf364846
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_maDensity_comp_affine_974c4adc07ab


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
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
theorem _root_.solution (M T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef)
    (hT : ∀ j : Fin e, T 0 j.succ = 0) (hdet : T.det ≠ 0) :
    chartMass (Tᴴ * M * T) = chartMass M := by
  have ht : T 0 0 ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, zero_mul])
  have hC : (T.submatrix Fin.succ Fin.succ).det ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, mul_zero])
  set C := (T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ with hCdef
  set c : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) with hcdef
  have hC' : C.det ≠ 0 := by
    rw [hCdef, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hC
  have hfun : hermChartPot (Tᴴ * M * T) = fun y => hermChartPot M (c + C *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj M T hM hT ht)
  unfold chartMass
  rw [hfun]
  simp_rw [maDensity_comp_affine (hermChartPot M) c C hC']
  rw [integral_const_mul, integral_comp_affine (maDensity fun _ => hermChartPot M) c C hC', ← mul_assoc,
    mul_inv_cancel₀ (Complex.normSq_pos.mpr hC').ne', one_mul]
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
