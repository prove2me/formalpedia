-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckePhaseFilter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:27:46.689957+00:00
-- url     : https://prove2.me/submissions/388dead9-efed-4a52-8be2-29ec51f14cf6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_inflate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_mask_sum
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
theorem _root_.solution (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (∑ j : Fin p,ZMod.stdAddChar (j.val:ZMod p)^n)=if p∣n then (p:ℂ) else 0 := by
  have h := lpsChar_mask_sum p 1 (n:ℤ)
  simp only [Nat.cast_one,one_mul,Int.cast_natCast,ZMod.natCast_eq_zero_iff] at h
  rw [←h]
  apply Finset.sum_congr rfl
  intro j _
  have he := lpsChar_inflate p 1 ((j.val:ℤ)*(n:ℤ))
  simp only [Nat.cast_one,one_mul] at he
  rw [he]
  have hc := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=p)) n (j.val:ZMod p)
  simpa only [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,mul_comm] using hc.symm
end QEC.Coding.TannerLiftedProduct
