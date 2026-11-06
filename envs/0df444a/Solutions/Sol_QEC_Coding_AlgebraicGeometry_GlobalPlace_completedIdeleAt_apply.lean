-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:08:18.987002+00:00
-- url     : https://prove2.me/submissions/40d39c85-1b02-46d8-bfd2-e940bb75b19f

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
theorem _root_.solution (P : GlobalPlace k F)
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    completedIdeleAt (k := k) (F := F) P x = x P :=
  rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
