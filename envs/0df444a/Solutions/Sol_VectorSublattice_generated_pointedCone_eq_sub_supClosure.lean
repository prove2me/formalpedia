-- Prove2me | solution 1 for VectorSublattice.generated_pointedCone_eq_sub_supClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:52.532437+00:00
-- url     : https://prove2.me/submissions/e0cf9384-3e18-4590-a975-44294dfa60a9

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Theorems.Thm_VectorSublattice_isSublattice
public import Theorems.Thm_VectorSublattice_subset_generated
public import Theorems.Thm_VectorSublattice_generated_le

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open VectorSublattice
variable (Y : VectorSublattice X)
open scoped Pointwise
namespace VectorSublattice
theorem _root_.solution (C : PointedCone ℝ X) :
    (generated (C : Set X) : Set X)
      = supClosure (C : Set X) - supClosure (C : Set X) := by
  refine Set.Subset.antisymm ?_ ?_
  · have h : (C : Set X) ⊆ (sublatticeOfConeSupClosureDiff C : Set X) := fun x hx =>
      ⟨x, subset_supClosure hx, 0, subset_supClosure C.zero_mem, sub_zero x⟩
    exact generated_le h
  · rintro _ ⟨u, hu, v, hv, rfl⟩
    have hC : (C : Set X) ⊆ (generated (C : Set X) : Set X) := subset_generated _
    have h_sup : SupClosed (generated (C : Set X) : Set X) :=
      (generated (C : Set X)).isSublattice.supClosed
    have hu_gen := supClosure_min hC h_sup hu
    have hv_gen := supClosure_min hC h_sup hv
    exact (generated (C : Set X)).toSubmodule.sub_mem hu_gen hv_gen
end VectorSublattice
