-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradDens_le_d538323a449d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:32.053808+00:00
-- url     : https://prove2.me/submissions/c066073c-0fab-4f7f-82a5-313370a7125b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_dz_le_fef259233242
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradMat_eq_ccc0be16809b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_posSemidef_sub_vecMulVec_fa5c3756139b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_mdisc_cons_smul_one_ec0394516c8d
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_re_mono


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
theorem _root_.solution {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (y : Fin (n + 1) → ℂ) (hv : DifferentiableAt ℝ v y) (μ : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, (hessC (φ i) y).PosSemidef ∧
      (((μ : ℝ) : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - hessC (φ i) y).PosSemidef) :
    gradDens φ v v y ≤
      ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) * ((n + 1) * (‖fderiv ℝ v y‖ ^ 2 * μ ^ n)) := by
  set a : Fin (n + 1) → ℂ := fun j => dz j (cplx v) y with ha
  set l : ℝ := ∑ j, ‖a j‖ ^ 2 with hl
  have hmono := mdisc_re_mono (Fin.cons (gradMat v v y) fun i => hessC (φ i) y)
    (Fin.cons ((l : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      fun _ : Fin n => (μ : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    (by
      intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero]; rw [gradMat_eq hv]; exact posSemidef_vecMulVec_self_star a
      · simp only [Fin.cons_succ]; exact (hφ i).1)
    (by
      intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero]; rw [gradMat_eq hv]; exact posSemidef_sub_vecMulVec a
      · simp only [Fin.cons_succ]; exact (hφ i).2)
  rw [mdisc_cons_smul_one, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re] at hmono
  have hle : l ≤ (n + 1) * ‖fderiv ℝ v y‖ ^ 2 := by
    calc l ≤ ∑ _j : Fin (n + 1), ‖fderiv ℝ v y‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (norm_dz_le hv j) 2
      _ = _ := by simp
  unfold gradDens
  have hc : 0 ≤ ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) := by positivity
  refine mul_le_mul_of_nonneg_left (hmono.trans ?_) hc
  calc l * μ ^ n ≤ ((n + 1) * ‖fderiv ℝ v y‖ ^ 2) * μ ^ n := mul_le_mul_of_nonneg_right hle (pow_nonneg hμ n)
    _ = _ := by ring
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
