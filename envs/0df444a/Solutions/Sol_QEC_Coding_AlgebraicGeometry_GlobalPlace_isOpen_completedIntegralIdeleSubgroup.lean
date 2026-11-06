-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.isOpen_completedIntegralIdeleSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:26:02.079832+00:00
-- url     : https://prove2.me/submissions/b7cd1fc0-ed58-45c3-b060-34c04a543951

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
    (S : Finset (GlobalPlace k F)) :
    IsOpen (completedIntegralIdeleSubgroup (k := k) (F := F) S :
      Set (CompletedGlobalIdele (k := k) (F := F))) := by
  exact RestrictedProduct.isOpen_forall_imp_mem
    (fun P ↦ isOpen_localUnitGroup P)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
