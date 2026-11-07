-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:54:11.357887+00:00
-- url     : https://prove2.me/submissions/9bf5f8e1-dd1a-490b-8dac-60fa05129cda

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibre_pullbackChart_reduced

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (hpN : ¬ p ∣ N) : _root_.AlgebraicGeometry.IsReduced (lpsOriginalSpecialFibre p N hN) := by
  let D := lpsOriginalIntegerNormalSchemeGlueData N hN
  let U := D.openCover.pullback₁
    (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p))
  let : ∀ b, _root_.AlgebraicGeometry.IsReduced (U.X b) := fun b => by
    change _root_.AlgebraicGeometry.IsReduced
      (pullback (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN)
        (lpsOriginalPrimeSpecToInteger p)) (lpsOriginalIntegerNormalGluedChartMap N hN b))
    let := lpsOriginalSpecialFibre_pullbackChart_reduced N hN p hpN b
    exact isReduced_of_isOpenImmersion
      (pullbackSymmetry (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN)
        (lpsOriginalPrimeSpecToInteger p)) (lpsOriginalIntegerNormalGluedChartMap N hN b)).hom
  exact _root_.AlgebraicGeometry.IsReduced.of_openCover _ U
end QEC.Coding.TannerLiftedProduct
