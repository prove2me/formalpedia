-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondFinrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:57:20.194936+00:00
-- url     : https://prove2.me/submissions/4fa7350e-b3a0-4bad-a6bb-1d44419769b5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_firstFinrank
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
    Module.finrank (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) = p+1 := by
  let R := LPSOriginalGaussAffineOrder N hN p
  let C := LPSOriginalRelativeGaussNormalization N p hNp h4N hN
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  have h := @Algebra.finrank_eq_of_equiv_equiv R C _ _
    (lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN) R C _ _ (lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN)
    (lpsOriginalGaussFrickeRingEquiv N hN p hpN)
    (lpsOriginalRelativeGaussNormalizationFrickeRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first N p hNp h4N hN hpN).symm
  exact h.symm.trans (lpsOriginalRelativeGaussNormalization_firstFinrank N p hNp h4N hN hpN)
end QEC.Coding.TannerLiftedProduct
