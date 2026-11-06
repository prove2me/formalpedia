-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.regularAt_iff_order_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:42:49.221204+00:00
-- url     : https://prove2.me/submissions/1909f502-835b-43d6-ba78-8fee20badc4b

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (P : GlobalPlace k F) {f : F} (hf : f ≠ 0) :
    RegularAt P f ↔ 0 ≤ order P f := by
  change P.valuation f ≤ 1 ↔ 0 ≤ -WithZero.log (P.valuation f)
  rw [neg_nonneg]
  symm
  simpa using WithZero.log_le_iff_le_exp ((P.valuation).ne_zero_iff.mpr hf) (a := 0)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
