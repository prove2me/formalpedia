-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:16:25.422216+00:00
-- url     : https://prove2.me/submissions/d7dd13e9-52fa-4342-b7d8-7aa95c6cf038

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
theorem _root_.solution (P : GlobalPlace k F) (f : F) :
    order P f⁻¹ = -order P f := by
  unfold order
  rw [(P.valuation).map_inv, WithZero.log_inv]
end QEC.Coding.AlgebraicGeometry.GlobalPlace
