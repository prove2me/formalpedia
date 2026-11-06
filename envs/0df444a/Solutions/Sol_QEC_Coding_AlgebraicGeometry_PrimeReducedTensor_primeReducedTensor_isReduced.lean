-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.primeReducedTensor_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:56:42.652732+00:00
-- url     : https://prove2.me/submissions/a63bc94f-3539-42c7-970a-dab8bdebcfe3

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedTensor_primeFrobeniusAlgHom_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedTensor_isReduced_of_primeFrobeniusAlgHom_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedTensor_primeFrobeniusAlgHom_tensor_eq_map

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
open scoped TensorProduct
noncomputable section
variable (p : ℕ) [Fact p.Prime]
namespace QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
theorem _root_.solution
    (C D : Type*) [CommRing C] [CommRing D]
    [Algebra (ZMod p) C] [Algebra (ZMod p) D]
    [IsReduced C] [IsReduced D] : IsReduced (C ⊗[ZMod p] D) := by
  apply isReduced_of_primeFrobeniusAlgHom_injective p
  rw [primeFrobeniusAlgHom_tensor_eq_map]
  change Function.Injective (TensorProduct.map
    (primeFrobeniusAlgHom p C).toLinearMap
    (primeFrobeniusAlgHom p D).toLinearMap)
  exact TensorProduct.map_injective_of_flat_flat _ _
    (primeFrobeniusAlgHom_injective p C)
    (primeFrobeniusAlgHom_injective p D)
end QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
