-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsCuspHecke_prime_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:46:44.673138+00:00
-- url     : https://prove2.me/submissions/75e95db4-6d03-4f95-9121-cdd693fb190e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsCuspHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (r : ℕ) :
    PowerSeries.coeff (p^(r+1)) (UpperHalfPlane.qExpansion 1 f)=
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 (lpsCuspHecke N p hNp f))-
        if r=0 then 0 else (p:ℂ)*PowerSeries.coeff (p^(r-1)) (UpperHalfPlane.qExpansion 1 f) := by
  rw [coeff_qExpansion_lpsCuspHecke]
  cases r with
  | zero =>
    have hd : ¬p∣1 := (Fact.out : p.Prime).not_dvd_one
    simp [lpsModularDilationCoefficient,hd]
  | succ r =>
    have hp : 0<p := (Fact.out : p.Prime).pos
    have hd : p∣p^(r+1) := by rw [pow_succ];exact dvd_mul_left p (p^r)
    have he : p^(r+1)/p=p^r := by rw [pow_succ,Nat.mul_div_cancel _ hp]
    change PowerSeries.coeff (p^(r+1+1)) (UpperHalfPlane.qExpansion 1 f)=_
    rw [lpsModularDilationCoefficient,if_pos hd,he]
    simp only [Nat.succ_ne_zero,if_false,Nat.succ_sub_one]
    rw [pow_succ,mul_comm p (p^(r+1))]
    exact (add_sub_cancel_right _ _).symm
end QEC.Coding.TannerLiftedProduct
