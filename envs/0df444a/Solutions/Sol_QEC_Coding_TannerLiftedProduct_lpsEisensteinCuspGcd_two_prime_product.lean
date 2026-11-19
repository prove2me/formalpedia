-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_two_prime_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:40:28.577216+00:00
-- url     : https://prove2.me/submissions/f8c3294b-4d9a-4f9f-b2a2-c14636e8d320

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntGcd_coprime_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsStandardThetaModularForm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a b : ℕ) (γ : SL(2,ℤ)) :
    Int.gcd ((2^a*q^b:ℕ):ℤ) (γ 1 0)=
      Int.gcd ((2^a:ℕ):ℤ) (γ 1 0)*Int.gcd ((q^b:ℕ):ℤ) (γ 1 0) := by
  have hc := ((Fact.out : q.Prime).odd_of_ne_two hq2).coprime_two_left.pow a b
  have hI : Int.gcd ((2^a:ℕ):ℤ) ((q^b:ℕ):ℤ)=1 := by
    simpa only [Int.gcd_def,Int.natAbs_natCast] using hc.gcd_eq_one
  rw [Nat.cast_mul,Int.gcd_comm,lpsIntGcd_coprime_mul _ _ _ hI]
  rw [Int.gcd_comm (γ 1 0),Int.gcd_comm (γ 1 0)]
end QEC.Coding.TannerLiftedProduct
