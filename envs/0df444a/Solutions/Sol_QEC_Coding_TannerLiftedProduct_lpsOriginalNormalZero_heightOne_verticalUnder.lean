-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_heightOne_verticalUnder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:34:30.43792+00:00
-- url     : https://prove2.me/submissions/63278af7-5d03-4e7f-8894-1f228e9e3c81

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOne_primeUnder_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerBaseFractionMap_injective
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
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime
attribute [local instance] QEC.Coding.TannerLiftedProduct.verticalPrimeJAlgebra
variable (N : ℕ) (hN : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.verticalPrimeBaseFieldAlgebra
local notation "K" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "C" => integralClosure (Polynomial ℤ) K
attribute [local instance] QEC.Coding.TannerLiftedProduct.verticalPrimeNormalCommRing
attribute [local instance] QEC.Coding.TannerLiftedProduct.verticalPrimeNormalRing
attribute [local instance] QEC.Coding.TannerLiftedProduct.verticalPrimeNormalSemiring
include hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (q : Ideal C) [q.IsPrime]
    (hq : q.height = 1) (hpq : (p : C) ∈ q) :
    q.under (Polynomial ℤ) = lpsOriginalGaussPrime p := by
  have hiK : Function.Injective (algebraMap (Polynomial ℤ) K) :=
    (algebraMap (FractionRing (Polynomial ℚ)) K).injective.comp
      lpsOriginalIntegerBaseFractionMap_injective
  let : FaithfulSMul (Polynomial ℤ) C :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial ℤ) C).mpr (fun f g h => by
      apply hiK
      exact congrArg (fun c : C => c.val) h)
  have hle : lpsOriginalGaussPrime p ≤ q.under (Polynomial ℤ) := by
    rw [lpsOriginalGaussPrime_eq_span,Ideal.span_singleton_le_iff_mem]
    change algebraMap (Polynomial ℤ) C (Polynomial.C (p : ℤ)) ∈ q
    simpa using hpq
  exact QEC.Coding.AlgebraicGeometry.heightOne_primeUnder_eq
    (lpsOriginalGaussPrime p) (lpsOriginalGaussPrime_ne_bot p) q hq hle
end QEC.Coding.TannerLiftedProduct
