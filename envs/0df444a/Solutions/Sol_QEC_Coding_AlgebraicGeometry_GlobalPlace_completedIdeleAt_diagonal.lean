-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleAt_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:43:47.127945+00:00
-- url     : https://prove2.me/submissions/ac2bc256-f40c-46af-bb04-b988ba07ae36

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalIdele

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped RestrictedProduct WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (u : Fˣ) (P : GlobalPlace k F) :
    completedIdeleAt (k := k) (F := F) P
        (completedIdeleDiagonal (k := k) (F := F) u) =
      P.completionUnitsEmbedding u :=
  rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
