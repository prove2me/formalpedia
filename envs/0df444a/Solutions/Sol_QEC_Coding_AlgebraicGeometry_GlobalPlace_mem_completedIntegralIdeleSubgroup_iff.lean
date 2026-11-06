-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_completedIntegralIdeleSubgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:25:59.073039+00:00
-- url     : https://prove2.me/submissions/a243469a-7fc9-4e39-8a89-7a6c972f468c

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
    (S : Finset (GlobalPlace k F))
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    x ∈ completedIntegralIdeleSubgroup S ↔
      ∀ P, P ∉ S → x P ∈ P.LocalUnitGroup :=
  Iff.rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
