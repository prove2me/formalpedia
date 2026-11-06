-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_completedIntegralIdeleSubgroup_iff_nonintegralPlaces_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:27:13.937571+00:00
-- url     : https://prove2.me/submissions/766f1f9c-f652-42be-ae5c-fa32c692d0ab

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalIdele
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_ideleNonintegralPlaces_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_completedIntegralIdeleSubgroup_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedDiagonal_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedDiagonal_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_ideleNonintegralPlaces_iff

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
      ideleNonintegralPlaces x ⊆ S := by
  classical
  rw [mem_completedIntegralIdeleSubgroup_iff]
  constructor
  · intro hx P hP
    by_contra hPS
    exact (mem_ideleNonintegralPlaces_iff x P).mp hP (hx P hPS)
  · intro hx P hPS
    by_contra hPunit
    have hP : P ∈ ideleNonintegralPlaces x :=
      (mem_ideleNonintegralPlaces_iff x P).mpr hPunit
    exact hPS (hx hP)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
