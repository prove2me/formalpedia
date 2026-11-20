-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:57:53.163748+00:00
-- url     : https://prove2.me/submissions/dc2cee54-1e6e-4380-84c4-fb0452e0a8a8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFreeOfRingEquivs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_firstFree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    Module.Free (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let R := LPSOriginalGaussAffineOrder N hN p
  let C := LPSOriginalRelativeGaussNormalization N p hNp h4N hN
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  let h := lpsOriginalRelativeGaussNormalization_firstFree N p hNp h4N hN hpN
  refine @lpsOriginalFreeOfRingEquivs R C R C _ _ _ _
    (lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN) (lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN)
    (lpsOriginalGaussFrickeRingEquiv N hN p hpN)
    (lpsOriginalRelativeGaussNormalizationFrickeRingEquiv N p hNp h4N hN hpN) ?_ h
  exact (lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first N p hNp h4N hN hpN).symm
end QEC.Coding.TannerLiftedProduct
