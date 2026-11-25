-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_dz_le_fef259233242
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:40.070541+00:00
-- url     : https://prove2.me/submissions/e29e93e7-c51f-4d08-a080-4099685af99c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_fderiv_cplx_5349c035cb13

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
open ReciprocityTheory.AnForm.A
namespace GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
theorem _root_.solution {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hv : DifferentiableAt ℝ v z)
    (j : Fin D) : ‖dz j (cplx v) z‖ ≤ ‖fderiv ℝ v z‖ := by
  simp only [dz, fderiv_cplx hv]
  have h1 : ‖(Pi.single j (1 : ℂ) : Fin D → ℂ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have h2 : ‖(Complex.I • Pi.single j (1 : ℂ) : Fin D → ℂ)‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_I, one_mul]; exact h1
  have hn := norm_nonneg (fderiv ℝ v z)
  have b1 := ((fderiv ℝ v z).le_opNorm (Pi.single j 1)).trans (mul_le_of_le_one_right hn h1)
  have b2 := ((fderiv ℝ v z).le_opNorm (Complex.I • Pi.single j 1)).trans (mul_le_of_le_one_right hn h2)
  have ht := norm_sub_le ((fderiv ℝ v z (Pi.single j 1) : ℂ))
    (Complex.I * (fderiv ℝ v z (Complex.I • Pi.single j 1) : ℂ))
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real] at ht
  rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
  linarith
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
