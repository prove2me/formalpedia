-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegral_of_prime_multiple_and_gaussIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:36:51.832722+00:00
-- url     : https://prove2.me/submissions/36c14241-43c7-469a-bc59-615916a224ad

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Prime.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_integral_of_prime_multiple_and_localizedIntegral
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
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring verticalPrimeJAlgebra
  verticalPrimeBaseFieldAlgebra verticalPrimeNormalCommRing verticalPrimeNormalRing
  verticalPrimeNormalSemiring
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    ∀ y : lpsOriginalGeneratedFunctionFieldQ N hN,
      IsIntegral (Polynomial ℤ) ((p : lpsOriginalGeneratedFunctionFieldQ N hN)*y) →
      IsIntegral (LPSOriginalGaussBase p) y → IsIntegral (Polynomial ℤ) y := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let instRK := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let instGK := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  let R := Polynomial ℤ
  let G := LPSOriginalGaussBase p
  let K : Type := lpsOriginalGeneratedFunctionFieldQ N hN
  let J := FractionRing R
  let : SMul R K := instRK.toSMul
  let : SMul G K := instGK.toSMul
  let : IsScalarTower R G K := lpsOriginalGaussBase_scalarTower N hN p
  let : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr
    ((algebraMap (FractionRing (Polynomial ℚ)) K).injective.comp
      lpsOriginalIntegerBaseFractionMap_injective)
  let instJK : Algebra J K := FractionRing.liftAlgebra R K
  let : SMul J K := instJK.toSMul
  let : IsScalarTower R J K := FractionRing.isScalarTower_liftAlgebra R K
  let : IsScalarTower G J K := .of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply RingHom.ext
    intro f
    change algebraMap G K (algebraMap R G f) =
      algebraMap J K (algebraMap G J (algebraMap R G f))
    rw [← IsScalarTower.algebraMap_apply R G K,
      ← IsScalarTower.algebraMap_apply R G J,
      ← IsScalarTower.algebraMap_apply R J K])
  let : FaithfulSMul G K := (faithfulSMul_iff_algebraMap_injective G K).mpr (by
    rw [IsScalarTower.algebraMap_eq G J K]
    exact (algebraMap J K).injective.comp (IsFractionRing.injective G J))
  let : IsIntegrallyClosed G :=
    isIntegrallyClosed_of_isLocalization G (lpsOriginalGaussPrime p).primeCompl
      (lpsOriginalGaussPrime p).primeCompl_le_nonZeroDivisors
  change ∀ y : K, IsIntegral R ((p : K)*y) → IsIntegral G y → IsIntegral R y
  intro y hR hG
  have ha : Prime (Polynomial.C (p : ℤ)) := Polynomial.prime_C_iff.mpr
    (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime)))
  apply QEC.Coding.AlgebraicGeometry.integral_of_prime_multiple_and_localizedIntegral
    (lpsOriginalGaussPrime p) J K (Polynomial.C (p : ℤ))
    (lpsOriginalGaussPrime_eq_span p) ha y
  · simpa only [Polynomial.C_eq_natCast,map_natCast] using hR
  · exact hG
end QEC.Coding.TannerLiftedProduct
