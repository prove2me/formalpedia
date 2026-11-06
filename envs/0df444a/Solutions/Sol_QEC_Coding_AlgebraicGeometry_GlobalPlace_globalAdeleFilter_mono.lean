-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilter_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:20:17.119191+00:00
-- url     : https://prove2.me/submissions/f4d79208-d262-450a-8cab-9bbb5f91dfec

import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Filter.Cofinite
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped Polynomial RatFunc WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    globalAdeleFilter (k := k) (F := F) D ≤
      globalAdeleFilter (k := k) (F := F) E := by
  intro a ha P
  exact (ha P).trans (WithZero.exp_le_exp.mpr (hDE P))
end QEC.Coding.AlgebraicGeometry.GlobalPlace
