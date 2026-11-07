-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalization_gaussSpecialFiber_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:37:03.501301+00:00
-- url     : https://prove2.me/submissions/7efb42b9-adc7-4ba3-bd1b-ffb8f587bbf7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussNormalization_etale

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberBaseFieldAlgebra
local notation "D" => integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberNormalizationCommRing
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberNormalizationRing
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberNormalizationSemiring
include hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (hpN : ¬ p ∣ N) :
    IsReduced (D ⧸ (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p) D)) := by
  let := lpsOriginalGaussNormalization_etale N hN p hpN
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact Algebra.FormallyUnramified.isRadical_map_isMaximal (LPSOriginalGaussBase p)
    D (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p))
end QEC.Coding.TannerLiftedProduct
