-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalInfinity_primeIdeal_radical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:40:42.182197+00:00
-- url     : https://prove2.me/submissions/defa1c51-8c17-475b-8099-6baa21b8d27b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalIntegral_of_prime_multiple_and_gaussIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalization_gaussSpecialFiber_reduced
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
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    (Ideal.span {(p : integralClosure (Polynomial ℤ)
      (lpsOriginalGeneratedFunctionFieldQ N hN))}).IsRadical := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  let R := Polynomial ℤ
  let G := LPSOriginalGaussBase p
  let K : Type := lpsOriginalGeneratedFunctionFieldQ N hN
  let C : Type := integralClosure R K
  let D : Type := integralClosure G K
  let instCCommRing : CommRing C := inferInstance
  let : Ring C := instCCommRing.toRing
  let : CommSemiring C := instCCommRing.toCommSemiring
  let : Semiring C := instCCommRing.toCommSemiring.toSemiring
  let instRC : Algebra R C := (integralClosure R K).algebra
  let : SMul R C := instRC.toSMul
  let instDCommRing : CommRing D := gaussFiberNormalizationCommRing N hN p
  let : Ring D := instDCommRing.toRing
  let : CommSemiring D := instDCommRing.toCommSemiring
  let : Semiring D := instDCommRing.toCommSemiring.toSemiring
  let instGD : Algebra G D := (integralClosure G K).algebra
  let : SMul G D := instGD.toSMul
  let F : C →+* D := lpsOriginalIntegerNormalInfinityToGaussNormalization N hN p
  let Jp : Ideal D := Ideal.span {(p : D)}
  have hmax : IsLocalRing.maximalIdeal G = Ideal.span {(p : G)} := by
    calc
      IsLocalRing.maximalIdeal G =
          (lpsOriginalGaussPrime p).map (algebraMap R G) :=
        (Localization.AtPrime.map_eq_maximalIdeal (I := lpsOriginalGaussPrime p)).symm
      _ = (Ideal.span {Polynomial.C (p : ℤ)}).map (algebraMap R G) :=
        congrArg (Ideal.map (algebraMap R G)) (lpsOriginalGaussPrime_eq_span p)
      _ = Ideal.span {(p : G)} := by
        rw [Ideal.map_span,Set.image_singleton]
        simp only [map_natCast]
  have hJ : Jp = (IsLocalRing.maximalIdeal G).map (algebraMap G D) := by
    rw [hmax,Ideal.map_span,Set.image_singleton,map_natCast]
  have hred : IsReduced (D ⧸
      (IsLocalRing.maximalIdeal G).map (algebraMap G D)) :=
    lpsOriginalNormalization_gaussSpecialFiber_reduced N hN p hpN
  have hradD : ((IsLocalRing.maximalIdeal G).map (algebraMap G D)).IsRadical :=
    (Ideal.isRadical_iff_quotient_reduced _).mpr hred
  have hrad : Jp.IsRadical := hJ.symm ▸ hradD
  change (Ideal.span {(p : C)}).IsRadical
  intro x hx
  obtain ⟨n,hxn⟩ := hx
  have hxD : F x ∈ Jp := by
    apply hrad
    refine ⟨n,?_⟩
    have hmap := Ideal.mem_map_of_mem F hxn
    simpa only [Ideal.map_span,Set.image_singleton,map_natCast,map_pow] using hmap
  obtain ⟨d,hd⟩ := Ideal.mem_span_singleton.mp hxD
  have heq : (p : K)*d.val = x.val := by
    have h := congrArg (fun z : D => z.val) hd
    exact h.symm
  have hR : IsIntegral R ((p : K)*d.val) := heq.symm ▸ x.property
  have hG : (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).IsIntegralElem d.val :=
    (lpsOriginalGaussIntegral_reciprocalIntegral_iff N hN p d.val).mpr d.property
  have hi : IsIntegral R d.val :=
    lpsOriginalReciprocalIntegral_of_prime_multiple_and_gaussIntegral N hN p d.val hR hG
  apply Ideal.mem_span_singleton.mpr
  refine ⟨⟨d.val,hi⟩,?_⟩
  apply Subtype.ext
  exact heq.symm
end QEC.Coding.TannerLiftedProduct
