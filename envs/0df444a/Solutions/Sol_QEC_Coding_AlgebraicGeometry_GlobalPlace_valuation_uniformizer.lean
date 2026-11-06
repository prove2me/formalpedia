-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:02:23.58824+00:00
-- url     : https://prove2.me/submissions/939295e8-52e4-4558-bd17-845e4fa7d14a

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
theorem _root_.solution (P : GlobalPlace k F) :
    P.valuation P.uniformizer = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec (P.normalized (WithZero.exp (-1 : ℤ)))
end QEC.Coding.AlgebraicGeometry.GlobalPlace
