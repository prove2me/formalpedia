-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergy_proof_2d481867e789
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:10.990521+00:00
-- url     : https://prove2.me/submissions/9b40d264-0059-4e50-a307-5d81a0c1e448

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_nonneg_fadf2dd021f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_sqn_smul_7b55cce31069
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_contDiff_chartCutoff_60dfe149687f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_fderiv_chartCutoff_zero_eq_zero_d2cd05d3850b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hasCompactSupport_chartCutoff_zero_e61a96b7ce17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_norm_fderiv_chartCutoff_le_69838da594e8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hess_bound_bcf9207f9557
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradDens_le_d538323a449d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_finrank_eq_5a18b3f2a1cb

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
open ChartCutoffEnergyAlt
namespace GroundTheory.Heights₂.Heights
namespace ChartCutoffEnergy
theorem _root_.solution : ChartCutoffEnergy.Statement := by
  intro n T hT
  choose C hC0 hC using fun i => hess_bound (hT i)
  set C' : ℝ := ∑ i, C i with hC'
  have hC'0 : 0 ≤ C' := Finset.sum_nonneg fun i _ => hC0 i
  have hH : ∀ i y, (hessC (hermChartPot (T i)) y).PosSemidef ∧
      ((((C' / (1 + sqn y)) : ℝ) : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
        hessC (hermChartPot (T i)) y).PosSemidef := by
    intro i y
    refine ⟨(hC i y).1, ?_⟩
    have hle : C i ≤ C' := Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ i)
    have hd : 0 ≤ C' / (1 + sqn y) - C i / (1 + sqn y) := by
      rw [← sub_div]; exact div_nonneg (sub_nonneg.mpr hle) (by linarith [sqn_nonneg y])
    have h := (PosSemidef.one.smul (Complex.zero_le_real.mpr hd)).add (hC i y).2
    rw [show C' / (1 + sqn y) = (C' / (1 + sqn y) - C i / (1 + sqn y)) + C i / (1 + sqn y) by ring,
      Complex.ofReal_add, add_smul, add_sub_assoc]
    exact h
  set F : (Fin (n + 1) → ℂ) → ℝ := fun x => ‖fderiv ℝ (chartCutoff 0 : (Fin (n + 1) → ℂ) → ℝ) x‖ ^ 2 with hF
  have hFint : Integrable F := by
    have hcont : Continuous F := ((contDiff_chartCutoff 0).continuous_fderiv (by norm_num)).norm.pow 2
    have hsupp : HasCompactSupport F :=
      (hasCompactSupport_chartCutoff_zero.fderiv (𝕜 := ℝ)).comp_left (g := fun t => ‖t‖ ^ 2) (by simp)
    exact hcont.integrable_of_hasCompactSupport hsupp
  set K0 : ℝ := ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) * ((n + 1) * C' ^ n) with hK0
  have hK0n : 0 ≤ K0 := by positivity
  refine ⟨K0 * ∫ x, F x, fun k => ?_⟩
  set c : ℝ := ((k : ℝ) + 1)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  set g : (Fin (n + 1) → ℂ) → ℝ := fun y => K0 * c ^ (2 * n + 2) * F (c • y) with hg
  have hgint : Integrable g := (hFint.comp_smul hc0.ne').const_mul _
  have hgI : ∫ y, g y = K0 * ∫ x, F x := by
    simp only [hg]
    rw [integral_const_mul, Measure.integral_comp_smul, finrank_eq, smul_eq_mul,
      abs_of_pos (by positivity), mul_assoc, ← mul_assoc (c ^ (2 * n + 2)), mul_inv_cancel₀ (by positivity), one_mul]
  have hpt : ∀ y, ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ g y := by
    intro y
    have hS := sqn_nonneg y
    have hv : DifferentiableAt ℝ (chartCutoff k : (Fin (n + 1) → ℂ) → ℝ) y :=
      (contDiff_chartCutoff k).differentiable (by norm_num) y
    have h1 := gradDens_le _ _ y hv (C' / (1 + sqn y)) (div_nonneg hC'0 (by linarith)) (fun i => hH i y)
    have h2 := norm_fderiv_chartCutoff_le (D := n + 1) k y
    rw [← hc] at h2
    have h3 : ‖fderiv ℝ (chartCutoff k : (Fin (n + 1) → ℂ) → ℝ) y‖ ^ 2 ≤ c ^ 2 * F (c • y) := by
      simp only [hF]
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 : ‖fderiv ℝ (chartCutoff k : (Fin (n + 1) → ℂ) → ℝ) y‖ ^ 2 * (C' / (1 + sqn y)) ^ n ≤
        c ^ 2 * F (c • y) * (C' ^ n * c ^ (2 * n)) := by
      by_cases hF0 : F (c • y) = 0
      · have h0 : ‖fderiv ℝ (chartCutoff k : (Fin (n + 1) → ℂ) → ℝ) y‖ ^ 2 = 0 :=
          le_antisymm (by simpa [hF0] using h3) (by positivity)
        rw [h0, hF0]; simp
      · have hne : fderiv ℝ (chartCutoff 0 : (Fin (n + 1) → ℂ) → ℝ) (c • y) ≠ 0 := fun h =>
          hF0 (by simp [hF, h])
        have hs : 1 ≤ sqn (c • y) := by
          by_contra h
          push Not at h
          exact hne (fderiv_chartCutoff_zero_eq_zero h)
        rw [sqn_smul] at hs
        have hμ : C' / (1 + sqn y) ≤ C' * c ^ 2 := by
          rw [div_le_iff₀ (by linarith)]
          have : 1 ≤ c ^ 2 * (1 + sqn y) := by nlinarith [sq_nonneg c]
          nlinarith
        have hμ' : (C' / (1 + sqn y)) ^ n ≤ C' ^ n * c ^ (2 * n) := by
          calc _ ≤ (C' * c ^ 2) ^ n := pow_le_pow_left₀ (div_nonneg hC'0 (by linarith)) hμ n
            _ = _ := by rw [mul_pow, ← pow_mul]
        exact mul_le_mul h3 hμ' (by positivity) (by positivity)
    calc _ ≤ _ := h1
      _ ≤ ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
            ((n + 1) * (c ^ 2 * F (c • y) * (C' ^ n * c ^ (2 * n)))) := by gcongr
      _ = g y := by simp only [hg, hK0]; ring
  by_cases hi : Integrable (fun y =>
      ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y)
  · exact (integral_mono hi hgint hpt).trans hgI.le
  · rw [integral_undef hi]
    exact mul_nonneg hK0n (integral_nonneg fun x => by positivity)
end ChartCutoffEnergy
end GroundTheory.Heights₂.Heights
