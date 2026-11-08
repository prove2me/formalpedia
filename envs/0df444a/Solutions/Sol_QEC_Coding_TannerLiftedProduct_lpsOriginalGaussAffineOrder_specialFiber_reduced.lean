-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_specialFiber_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:23:55.423735+00:00
-- url     : https://prove2.me/submissions/ba06ff4c-8cbd-4490-af57-0569fcc4a11b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    IsReduced (LPSOriginalGaussAffineOrder N hN p ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))) := by
  let := lpsOriginalGaussAffineOrder_formallyUnramified N hN p hpN
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact Algebra.FormallyUnramified.isRadical_map_isMaximal (LPSOriginalGaussBase p)
    (LPSOriginalGaussAffineOrder N hN p) (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p))
end QEC.Coding.TannerLiftedProduct
