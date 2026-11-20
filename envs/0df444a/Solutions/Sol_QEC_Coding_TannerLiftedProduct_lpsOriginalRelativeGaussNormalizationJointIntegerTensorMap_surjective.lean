-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T12:02:21.898607+00:00
-- url     : https://prove2.me/submissions/85a50293-8ce9-474f-ba10-cac272aa6c75

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_jointClosure_eq_top
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJointTensorMap_surjective_of_jointClosure


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
    letI : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
    letI : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
    letI : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
    Function.Surjective (lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap N p hNp h4N hN hpN) := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  exact lpsOriginalJointTensorMap_surjective_of_jointClosure
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).toIntAlgHom
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).toIntAlgHom
    (lpsOriginalRelativeGaussNormalization_jointClosure_eq_top N p hNp h4N hN hpN)
end QEC.Coding.TannerLiftedProduct
