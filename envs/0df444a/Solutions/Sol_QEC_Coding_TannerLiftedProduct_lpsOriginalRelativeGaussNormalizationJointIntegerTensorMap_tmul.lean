-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:54:08.387068+00:00
-- url     : https://prove2.me/submissions/c3f5d8ec-8f04-45b1-ae92-5d4c22b0a302

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (u v : LPSOriginalGaussAffineOrder N hN p) :
    letI : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
    letI : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
    letI : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
    letI : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
    lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap N p hNp h4N hN hpN (u ⊗ₜ[ℤ] v) =
      lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN u *
        lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN v := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  rfl
end QEC.Coding.TannerLiftedProduct
