-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_fourierCoeff_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:32.544779+00:00
-- url     : https://prove2.me/submissions/13558a62-f8bb-4dfc-816c-67e60026cec5

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCuspHorocycle_coeff_norm_summable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleTerm_norm
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (k : ℤ) :
    HasSum (fun n : ℕ => fourierCoeff (lpsCuspHorocycleTerm N f y n) k)
      (fourierCoeff (lpsCuspHorocycleCircle N f y) k) := by
  let F (n : ℕ) (x : AddCircle (1:ℝ)) : ℂ := fourier (-k) x*lpsCuspHorocycleTerm N f y n x
  have hnorm (n : ℕ) (x : AddCircle (1:ℝ)) : ‖F n x‖=
      ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖*(Real.exp (-2*Real.pi*y))^n := by
    dsimp only [F]
    rw [norm_mul,fourier_apply,Circle.norm_coe,one_mul,lpsCuspHorocycleTerm_norm]
  have hcont (n : ℕ) : Continuous (F n) := by
    unfold F lpsCuspHorocycleTerm
    exact (map_continuous (fourier (-k))).mul
      (continuous_const.mul (map_continuous (fourier (n:ℤ))))
  have hi (n : ℕ) : Integrable (F n) (@AddCircle.haarAddCircle 1 ⟨by norm_num⟩) :=
    (hcont n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : Summable (fun n : ℕ => ∫ x : AddCircle (1:ℝ),‖F n x‖ ∂AddCircle.haarAddCircle) := by
    simp_rw [hnorm]
    simpa [integral_const] using
      lpsWeightTwoCuspHorocycle_coeff_norm_summable N f y hy
  have h := hasSum_integral_of_summable_integral_norm hi hsum
  have he (x : AddCircle (1:ℝ)) : (∑' n : ℕ,F n x)=
      fourier (-k) x*lpsCuspHorocycleCircle N f y x := by
    exact tsum_mul_left
  simp only [fourierCoeff,smul_eq_mul] at ⊢
  simpa only [F,he] using h
end QEC.Coding.TannerLiftedProduct
