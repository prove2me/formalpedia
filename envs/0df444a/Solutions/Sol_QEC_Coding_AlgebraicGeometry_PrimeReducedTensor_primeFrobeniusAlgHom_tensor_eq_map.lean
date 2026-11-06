-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.primeFrobeniusAlgHom_tensor_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:55:09.679205+00:00
-- url     : https://prove2.me/submissions/c5d8827f-ee08-4ea1-829b-e160ff8b52fd

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
    (C D : Type*) [CommRing C] [CommRing D]
    [Algebra (ZMod p) C] [Algebra (ZMod p) D] :
    primeFrobeniusAlgHom p (C ⊗[ZMod p] D) =
      Algebra.TensorProduct.map (primeFrobeniusAlgHom p C)
        (primeFrobeniusAlgHom p D) := by
  apply Algebra.TensorProduct.ext'
  intro c d
  change (c ⊗ₜ[ZMod p] d) ^ p = (c ^ p) ⊗ₜ[ZMod p] (d ^ p)
  exact Algebra.TensorProduct.tmul_pow c d p
end QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
