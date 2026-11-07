-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalInfinity_specialFiber_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:45:37.89461+00:00
-- url     : https://prove2.me/submissions/05e9a3df-7539-4255-adb2-96a738e14bf3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalInfinity_primeIdeal_radical

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
    IsReduced (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) ⧸
      Ideal.span {(p : integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))}) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  exact (Ideal.isRadical_iff_quotient_reduced _).mp
    (lpsOriginalNormalInfinity_primeIdeal_radical N hN p hpN)
end QEC.Coding.TannerLiftedProduct
