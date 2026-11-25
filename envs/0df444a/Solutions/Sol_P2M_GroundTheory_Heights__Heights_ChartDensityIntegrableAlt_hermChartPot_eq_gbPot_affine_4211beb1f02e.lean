-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_hermChartPot_eq_gbPot_affine_4211beb1f02e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:06:55.871503+00:00
-- url     : https://prove2.me/submissions/6cc2edbd-756f-4d2c-9733-03761ac99c76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_exists_conjTranspose_mul_self_3bc270d4f9d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_chart_quad_eq_395811d0abf6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_re_star_dotProduct_self_cd96284eeba4

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
namespace GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
theorem _root_.solution {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ∃ (c : Fin e → ℂ) (P : Matrix (Fin e) (Fin e) ℂ) (κ : ℝ), P.det ≠ 0 ∧
      hermChartPot M = fun y => gbPot (c + P *ᵥ y) + κ := by
  obtain ⟨C, hNC, hC⟩ := exists_conjTranspose_mul_self (hM.submatrix (Fin.succ_injective e))
  have hCH : Cᴴ.det ≠ 0 := by rw [det_conjTranspose]; exact star_ne_zero.mpr hC
  set w : Fin e → ℂ := fun i => M i.succ 0 with hw
  set d : Fin e → ℂ := (Cᴴ)⁻¹ *ᵥ w with hd'
  have hd : Cᴴ *ᵥ d = w := by
    rw [hd', mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hCH), one_mulVec]
  have hq := fun y => chart_quad_eq hM.1 hNC hd y
  set s : ℝ := (M 0 0 - star d ⬝ᵥ d).re with hs
  have hspos : 0 < s := by
    have hy0 : C *ᵥ (-(C⁻¹ *ᵥ d)) + d = 0 := by
      rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC), one_mulVec, neg_add_cancel]
    have hx : (Fin.cons 1 (-(C⁻¹ *ᵥ d)) : Fin (e + 1) → ℂ) ≠ 0 := fun h => by
      have := congr_fun h 0
      simp at this
    have hpos := hM.re_dotProduct_pos hx
    rw [hq, hy0] at hpos
    simpa [hs] using hpos
  set r : ℝ := Real.sqrt s with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hspos
  refine ⟨((r⁻¹ : ℝ) : ℂ) • d, ((r⁻¹ : ℝ) : ℂ) • C, Real.log r, ?_, ?_⟩
  · rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (inv_pos.mpr hrpos).ne')) hC
  · funext y
    have hX : 0 ≤ ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by positivity
    have hcy : ((r⁻¹ : ℝ) : ℂ) • d + (((r⁻¹ : ℝ) : ℂ) • C) *ᵥ y = ((r⁻¹ : ℝ) : ℂ) • (C *ᵥ y + d) := by
      rw [smul_mulVec, smul_add, add_comm]
    have hnorm : ∑ i, ‖(((r⁻¹ : ℝ) : ℂ) • (C *ᵥ y + d)) i‖ ^ 2 = (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hrpos), mul_pow]
    have hsq : s = r ^ 2 := (Real.sq_sqrt hspos.le).symm
    have h1pos : 0 < 1 + (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by positivity
    have hsplit : s + ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 = r ^ 2 * (1 + (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2) := by
      rw [hsq]; field_simp
    simp only [hermChartPot, gbPot]
    rw [hq, Complex.add_re, ← hs, re_star_dotProduct_self, hcy, hnorm, hsplit,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hrpos.le,
      Real.log_mul hrpos.ne' (Real.sqrt_pos.mpr h1pos).ne']
    ring
end GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
