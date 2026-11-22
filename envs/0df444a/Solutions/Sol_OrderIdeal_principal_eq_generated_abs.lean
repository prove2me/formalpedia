-- Prove2me | solution 1 for OrderIdeal.principal_eq_generated_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:28:31.501801+00:00
-- url     : https://prove2.me/submissions/28464b96-7140-46cb-b49b-252ee9c595ee

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Theorems.Thm_OrderIdeal_generated_le
public import Theorems.Thm_VectorSublattice_generated_le


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)
namespace OrderIdeal
theorem _root_.solution (a : X) :
    principal a = generated ({|a|} : Set X) := by
  refine le_antisymm (fun x hx => ?_) (generated_le ?_)
  · obtain ⟨c, hc, hxle⟩ := hx
    refine (mem_sInf (S := {J : OrderIdeal X | {|a|} ⊆ (J : Set X)})).mpr fun J hJ => ?_
    have ha : |a| ∈ J := hJ rfl
    have hca : c • |a| ∈ J := J.toSubmodule.smul_mem c ha
    exact J.mem_of_abs_mem (J.solid hca (abs_nonneg _) hxle)
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨1, zero_le_one, by rw [abs_abs, one_smul]⟩
end OrderIdeal
