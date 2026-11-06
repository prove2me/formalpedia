-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.residue_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:17:02.477421+00:00
-- url     : https://prove2.me/submissions/377abf0b-89aa-4d8a-8599-cf4b8f38d06c

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
theorem _root_.solution (P : GlobalPlace k F) (f : valuationRing P) :
    residue P f = 0 ↔ f ∈ IsLocalRing.maximalIdeal (valuationRing P) :=
  IsLocalRing.residue_eq_zero_iff f
end QEC.Coding.AlgebraicGeometry.GlobalPlace
