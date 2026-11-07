-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_parseval_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:12:06.527201+00:00
-- url     : https://prove2.me/submissions/dda82340-36e0-475b-99e8-f7aac041c92c

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_fourierCoeff_nat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_fourierCoeff_neg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_parseval_int

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
      (Real.exp (-2*Real.pi*y))^(2*n))
      (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle) := by
  have hneg (k : ℤ) (hk : k∉Set.range (fun n : ℕ => (n:ℤ))) :
      ‖fourierCoeff (lpsCuspHorocycleCircle N f y) k‖^2=0 := by
    have hk' : k<0 := by
      by_contra hc
      apply hk
      exact ⟨k.toNat,Int.toNat_of_nonneg (by omega)⟩
    rw [lpsCuspHorocycleCircle_fourierCoeff_neg N f y hy k hk',norm_zero,zero_pow (by norm_num)]
  have h := (Int.ofNat_injective.hasSum_iff hneg).mpr
    (lpsCuspHorocycleCircle_parseval_int N f y hy)
  apply h.congr_fun
  intro n
  change _=‖fourierCoeff (lpsCuspHorocycleCircle N f y) (n:ℤ)‖^2
  rw [lpsCuspHorocycleCircle_fourierCoeff_nat N f y hy,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,Real.abs_exp,mul_pow,←pow_mul]
  congr 1
  congr 1
  omega
end QEC.Coding.TannerLiftedProduct
