-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.order_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:33:51.183475+00:00
-- url     : https://prove2.me/submissions/cb9f7b73-e390-4937-8c95-5b1f9ff36eee

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_trivialOnConstants

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (P : GlobalPlace k F) (a : k) (ha : a ≠ 0) :
    order P (algebraMap k F a) = 0 := by
  simp [order, (trivialOnConstants P).eq_one a ha]
end QEC.Coding.AlgebraicGeometry.GlobalPlace
