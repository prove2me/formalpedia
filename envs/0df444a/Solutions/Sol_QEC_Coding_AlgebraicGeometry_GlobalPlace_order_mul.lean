-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.order_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:16:18.328578+00:00
-- url     : https://prove2.me/submissions/06fab019-93af-48fc-8f17-5616eca36bfe

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
theorem _root_.solution (P : GlobalPlace k F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    order P (f * g) = order P f + order P g := by
  unfold order
  rw [(P.valuation).map_mul f g,
    WithZero.log_mul ((P.valuation).ne_zero_iff.mpr hf)
      ((P.valuation).ne_zero_iff.mpr hg)]
  ring
end QEC.Coding.AlgebraicGeometry.GlobalPlace
