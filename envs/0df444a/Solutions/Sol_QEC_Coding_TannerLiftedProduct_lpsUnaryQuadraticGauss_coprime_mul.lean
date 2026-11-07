-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_coprime_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:56:17.692882+00:00
-- url     : https://prove2.me/submissions/04c8b2bf-a9d8-40be-b0ad-622006f23611

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCRT_linear_bijective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticChar_product_split
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_eq_Gauss
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticPhase_stdAddChar
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ℤ) :
    lpsUnaryQuadraticGauss a (m*n) =
      lpsUnaryQuadraticGauss (a*(n:ℤ)) m * lpsUnaryQuadraticGauss (a*(m:ℤ)) n := by
  classical
  rw [← lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier]
  simp only [zero_mul,add_zero]
  let f := fun r : Fin m × Fin n => ((n*r.1.val+m*r.2.val:ℕ):ZMod (m*n))
  let g := fun r : ZMod (m*n) => ZMod.stdAddChar ((a:ZMod (m*n))*r^2)
  have hs := Fintype.sum_bijective f (lpsCRT_linear_bijective m n h)
    (fun r => g (f r)) g (fun _ => rfl)
  change (∑ r : ZMod (m*n), g r)=_
  rw [← hs]
  dsimp only [f,g]
  rw [Fintype.sum_prod_type]
  unfold lpsUnaryQuadraticGauss
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  simp_rw [lpsQuadraticPhase_stdAddChar,← lpsFin_cast_finEquiv]
  have he := lpsQuadraticChar_product_split m n a x.val y.val
  convert he using 1 <;> push_cast <;> rfl
end QEC.Coding.TannerLiftedProduct
