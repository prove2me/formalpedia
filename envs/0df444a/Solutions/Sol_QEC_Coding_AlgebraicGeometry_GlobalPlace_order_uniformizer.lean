-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.order_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:30:32.532588+00:00
-- url     : https://prove2.me/submissions/4f3f4bb7-234f-41ee-9f35-e8a7c5945de0

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (P : GlobalPlace k F) : order P P.uniformizer = 1 := by
  rw [order, valuation_uniformizer]
  simp
end QEC.Coding.AlgebraicGeometry.GlobalPlace
