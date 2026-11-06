-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilter_inf_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:20:29.859862+00:00
-- url     : https://prove2.me/submissions/2c6055f2-6430-4563-a74b-ec8fba6a6f08

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
theorem _root_.solution (D : Divisor (GlobalPlace k F)) :
    globalAdeleFilter (k := k) (F := F) D ⊓
        diagonalAdeleSubmodule (k := k) (F := F) =
      Submodule.map (diagonalAdele (k := k) (F := F)) (riemannRochSubmodule D) := by
  ext a
  constructor
  · rintro ⟨ha, f, rfl⟩
    refine ⟨f, ?_, rfl⟩
    exact ha
  · rintro ⟨f, hf, rfl⟩
    exact ⟨hf, ⟨f, rfl⟩⟩
end QEC.Coding.AlgebraicGeometry.GlobalPlace
