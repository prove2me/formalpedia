-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.primeFrobeniusAlgHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:55:01.219313+00:00
-- url     : https://prove2.me/submissions/82f742b1-0107-4e3a-b051-e65a3f2f389e

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
open scoped TensorProduct
noncomputable section
variable (p : ℕ) [Fact p.Prime]
namespace QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
theorem _root_.solution
    (C : Type*) [CommRing C] [Algebra (ZMod p) C] [IsReduced C] :
    Function.Injective (primeFrobeniusAlgHom p C) := by
  intro x y h
  apply sub_eq_zero.mp
  apply IsReduced.eq_zero _
  refine ⟨p, ?_⟩
  change primeAlgebraFrobenius p C (x - y) = 0
  change primeAlgebraFrobenius p C x = primeAlgebraFrobenius p C y at h
  rw [map_sub, h, sub_self]
end QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
