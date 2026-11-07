-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_specialFiber_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:43:38.942098+00:00
-- url     : https://prove2.me/submissions/2d850c9c-4106-48ef-ac7c-443088b4632d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Prime.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalZero_primeIdeal_radical

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
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    IsReduced (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) ⧸
      Ideal.span {(p : integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))}) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact (Ideal.isRadical_iff_quotient_reduced _).mp
    (lpsOriginalNormalZero_primeIdeal_radical N hN p hpN)
end QEC.Coding.TannerLiftedProduct
