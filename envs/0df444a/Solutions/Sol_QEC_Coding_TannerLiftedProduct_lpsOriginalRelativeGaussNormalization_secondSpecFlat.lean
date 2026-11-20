-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondSpecFlat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T12:04:59.847708+00:00
-- url     : https://prove2.me/submissions/29ded3f6-0fed-4f3f-9ee2-3569e2ff9be1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondFlat

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    AlgebraicGeometry.Flat (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN))) := by
  apply AlgebraicGeometry.Flat.SpecMap_iff.mpr
  exact lpsOriginalRelativeGaussNormalization_secondFlat N p hNp h4N hN hpN
end QEC.Coding.TannerLiftedProduct
