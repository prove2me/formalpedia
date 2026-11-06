-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ValuationBound.space_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:50.772682+00:00
-- url     : https://prove2.me/submissions/e5856db8-1d24-451d-b9e8-a60f68e28ff5

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.ValuationBound
variable {k F P : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.ValuationBound
theorem _root_.solution (valuations : P → Valuation F ℤᵐ⁰) {G H : Divisor P}
    (hGH : G ≤ H) : space (k := k) valuations G ≤ space (k := k) valuations H := by
  intro f hf place
  exact (hf place).trans (WithZero.exp_le_exp.mpr (hGH place))
end QEC.Coding.AlgebraicGeometry.ValuationBound
