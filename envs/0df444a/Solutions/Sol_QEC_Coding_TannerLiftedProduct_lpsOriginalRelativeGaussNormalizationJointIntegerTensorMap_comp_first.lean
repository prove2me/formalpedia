-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap_comp_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:54:31.607614+00:00
-- url     : https://prove2.me/submissions/ac00631e-50aa-493d-a51d-00be15ea8c4e

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
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)) =
        lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  apply RingHom.ext
  intro u
  change (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN u) *
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN 1) = _
  rw [map_one, mul_one]
end QEC.Coding.TannerLiftedProduct
