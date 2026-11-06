-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_completedEverywhereIntegralIdeleSubgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:43:50.624591+00:00
-- url     : https://prove2.me/submissions/f88caffc-5276-43bf-b70f-c80c60640307

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalIdele
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_completedIntegralIdeleSubgroup_iff_nonintegralPlaces_subset

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped RestrictedProduct WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    x ∈ completedEverywhereIntegralIdeleSubgroup ↔
      ideleNonintegralPlaces x = ∅ := by
  rw [show x ∈ completedEverywhereIntegralIdeleSubgroup ↔
      ideleNonintegralPlaces x ⊆ ∅ from
    mem_completedIntegralIdeleSubgroup_iff_nonintegralPlaces_subset ∅ x]
  exact Finset.subset_empty
end QEC.Coding.AlgebraicGeometry.GlobalPlace
