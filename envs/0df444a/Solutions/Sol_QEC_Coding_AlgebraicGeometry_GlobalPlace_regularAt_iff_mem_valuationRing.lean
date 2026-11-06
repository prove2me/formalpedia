-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.regularAt_iff_mem_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:42:48.478978+00:00
-- url     : https://prove2.me/submissions/94d57519-c8c5-41c6-aacc-2d476ba4c53c

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
    RegularAt P f ↔ f ∈ valuationRing P :=
  (mem_valuationRing_iff P f).symm
end QEC.Coding.AlgebraicGeometry.GlobalPlace
