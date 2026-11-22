-- Prove2me | solution 1 for OrderIdeal.strongOrderUnit_iff_principal_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:28:20.787788+00:00
-- url     : https://prove2.me/submissions/290f4f13-33a9-4446-bcf5-812cc8c9ecbf

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Theorems.Thm_VectorSublattice_mem_top
attribute [local simp] VectorSublattice.mem_top



set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (a : X)
namespace OrderIdeal
theorem _root_.solution {e : X} :
    StrongOrderUnit e ↔ 0 ≤ e ∧ principal e = ⊤ := by
  refine ⟨fun ⟨he, hdom⟩ => ⟨he, ?_⟩, fun ⟨he, htop⟩ => ⟨he, fun x => ?_⟩⟩
  · refine SetLike.ext fun x => iff_of_true ?_ mem_top
    obtain ⟨c, hc, hxc⟩ := hdom x
    exact ⟨c, hc, by rwa [abs_of_nonneg he]⟩
  · have hx : x ∈ principal e := htop ▸ mem_top
    obtain ⟨c, hc, hxc⟩ := hx
    exact ⟨c, hc, by rwa [abs_of_nonneg he] at hxc⟩
end OrderIdeal
