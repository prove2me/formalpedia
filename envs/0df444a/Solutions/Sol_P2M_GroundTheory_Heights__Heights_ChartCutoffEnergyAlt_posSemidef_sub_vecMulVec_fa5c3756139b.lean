-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_posSemidef_sub_vecMulVec_fa5c3756139b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:41.832593+00:00
-- url     : https://prove2.me/submissions/2716e4a1-80e0-4827-b7bd-30259e2a5c79

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy

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
theorem _root_.solution {D : ℕ} (a : Fin D → ℂ) :
    (((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - vecMulVec a (star a)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨(isHermitian_one.smul ?_).sub (posSemidef_vecMulVec_self_star a).1, fun x => ?_⟩
  · show star ((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ) = ((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ)
    simp
  set w : ℂ := star a ⬝ᵥ x with hw
  have hform : star x ⬝ᵥ ((((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - vecMulVec a (star a)) *ᵥ x)
      = (((∑ j, ‖a j‖ ^ 2) * (∑ j, ‖x j‖ ^ 2) - ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, dotProduct_sub, dotProduct_smul,
      op_smul_eq_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have h1 : star x ⬝ᵥ x = ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.star_def]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have h2 : star x ⬝ᵥ a = star w := by
      simp only [hw, dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h1, h2, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [hform]
  refine Complex.zero_le_real.mpr (sub_nonneg.mpr ?_)
  have hcs : ‖w‖ ≤ ∑ j, ‖a j‖ * ‖x j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Pi.star_apply]
  have hcs2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖x j‖)
  calc ‖w‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖x j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcs 2
    _ ≤ _ := hcs2
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
