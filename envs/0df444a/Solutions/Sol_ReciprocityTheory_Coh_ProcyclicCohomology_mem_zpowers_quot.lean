-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.mem_zpowers_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:33.261803+00:00
-- url     : https://prove2.me/submissions/c94bce1e-87d1-4cc1-9d5c-4a8f1eb6c00a

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Coh.ProcyclicCohomology
open Topology
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {s : G}
namespace ReciprocityTheory.Coh.ProcyclicCohomology
theorem _root_.solution (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} [W.Normal]
    (hW : IsOpen (W : Set G)) (x : G ⧸ W) : x ∈ Subgroup.zpowers (QuotientGroup.mk' W s) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hU : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (W : Set G)) :=
    hW.preimage (continuous_const.mul continuous_id)
  obtain ⟨y, hyU, hy⟩ := hs.inter_open_nonempty _ hU ⟨g, by simp [W.one_mem]⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow, QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq.mpr hyU).symm
end ReciprocityTheory.Coh.ProcyclicCohomology
