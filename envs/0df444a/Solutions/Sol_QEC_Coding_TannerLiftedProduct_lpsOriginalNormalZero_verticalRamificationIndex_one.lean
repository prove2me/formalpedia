-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_verticalRamificationIndex_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:28:21.815804+00:00
-- url     : https://prove2.me/submissions/562ad3ee-67b2-4adf-bc82-0d7e6d51dee6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.Locus
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalVerticalUnramified
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalZero_verticalUnramified
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalAffine_finite


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring verticalPrimeJAlgebra
  verticalPrimeBaseFieldAlgebra verticalPrimeNormalCommRing verticalPrimeNormalRing
  verticalPrimeNormalSemiring
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
local notation "K" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "C" => integralClosure (Polynomial ℤ) K
local notation "D" => integralClosure (LPSOriginalGaussBase p) K
include hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hpN : ¬ p ∣ N) (q : Ideal C) [q.IsPrime] (hq : q.height = 1)
    (hpq : (p : C) ∈ q) : q.ramificationIdx (Polynomial ℤ) = 1 := by
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let := lpsOriginalIntegerNormalAffine_finite N hN
  let := lpsOriginalNormalZero_verticalUnramified N hN p hpN q hq hpq
  exact Ideal.ramificationIdx_eq_one q (Polynomial ℤ)
end QEC.Coding.TannerLiftedProduct
