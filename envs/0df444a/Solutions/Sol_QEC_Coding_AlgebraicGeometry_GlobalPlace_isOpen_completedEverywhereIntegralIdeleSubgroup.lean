-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.isOpen_completedEverywhereIntegralIdeleSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:43:55.749877+00:00
-- url     : https://prove2.me/submissions/b10cdfbc-7b39-4904-9c69-c8eb08b6d787

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalIdele
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_isOpen_completedIntegralIdeleSubgroup

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped RestrictedProduct WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution :
    IsOpen (completedEverywhereIntegralIdeleSubgroup (k := k) (F := F) :
      Set (CompletedGlobalIdele (k := k) (F := F))) :=
  isOpen_completedIntegralIdeleSubgroup ∅
end QEC.Coding.AlgebraicGeometry.GlobalPlace
