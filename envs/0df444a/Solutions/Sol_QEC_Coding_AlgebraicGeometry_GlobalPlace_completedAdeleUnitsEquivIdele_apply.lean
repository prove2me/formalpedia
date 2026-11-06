-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.completedAdeleUnitsEquivIdele_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:08:19.861494+00:00
-- url     : https://prove2.me/submissions/a18e4631-07f2-496e-8048-cf38963d357a

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
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (x : (CompletedGlobalAdele (k := k) (F := F))ˣ)
    (P : GlobalPlace k F) :
    completedAdeleUnitsEquivIdele (k := k) (F := F) x P = x.1 P :=
  rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
