-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap_comp_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:54:40.790177+00:00
-- url     : https://prove2.me/submissions/c9a13996-fdf2-400a-8d82-77afc98b5794

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
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
    letI : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
    letI : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
    letI : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
    (lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap N p hNp h4N hN hpN).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom =
        lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  apply RingHom.ext
  intro v
  change (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN 1) *
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN v) = _
  rw [map_one, one_mul]
end QEC.Coding.TannerLiftedProduct
