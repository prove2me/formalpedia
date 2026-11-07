-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_pullbackChart_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:51:43.360806+00:00
-- url     : https://prove2.me/submissions/c7bb5278-143d-4dfa-8d51-d33eecc66312

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimePullback_isReduced_of_quotient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalInfinity_specialFiber_reduced
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalZero_specialFiber_reduced


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (hpN : ¬ p ∣ N) (b : Bool) :
    _root_.AlgebraicGeometry.IsReduced
      (pullback (lpsOriginalIntegerNormalGluedChartMap N hN b)
        (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN)
          (lpsOriginalPrimeSpecToInteger p))) := by
  have h : _root_.AlgebraicGeometry.IsReduced
      (pullback (lpsOriginalIntegerNormalGluedChartMap N hN b ≫
        lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p)) := by
    cases b with
    | false =>
      exact lpsOriginalPrimePullback_isReduced_of_quotient
        (lpsOriginalIntegerNormalZeroChart N hN) p
        (lpsOriginalNormalZero_specialFiber_reduced N hN p hpN) _
    | true =>
      exact lpsOriginalPrimePullback_isReduced_of_quotient
        (lpsOriginalIntegerNormalInfinityChart N hN) p
        (lpsOriginalNormalInfinity_specialFiber_reduced N hN p hpN) _
  let := h
  exact isReduced_of_isOpenImmersion
    (pullbackRightPullbackFstIso (lpsOriginalIntegerNormalGluedToSpecZ N hN)
      (lpsOriginalPrimeSpecToInteger p) (lpsOriginalIntegerNormalGluedChartMap N hN b)).hom
end QEC.Coding.TannerLiftedProduct
