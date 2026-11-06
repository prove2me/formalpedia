-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.isReduced_of_primeFrobeniusAlgHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:55:08.820068+00:00
-- url     : https://prove2.me/submissions/e4f38cfd-03aa-42f1-b24b-8c619627ae40

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
    (C : Type*) [CommRing C] [Algebra (ZMod p) C]
    (h : Function.Injective (primeFrobeniusAlgHom p C)) : IsReduced C := by
  apply (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr
  intro x hx
  apply h
  change x ^ p = (0 : C) ^ p
  rw [hx, zero_pow (Fact.out : p.Prime).ne_zero]
end QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
