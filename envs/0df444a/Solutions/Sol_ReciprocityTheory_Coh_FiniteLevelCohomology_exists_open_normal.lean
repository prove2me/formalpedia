-- Prove2me | solution 1 for ReciprocityTheory.Coh.FiniteLevelCohomology.exists_open_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:57:46.274043+00:00
-- url     : https://prove2.me/submissions/4b95d226-5576-4b5f-9802-2f888c707c69

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_exists_nhds_right_const
import Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_stab_mem_nhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
open ReciprocityTheory.Coh.FiniteLevelCohomology
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.FiniteLevelCohomology
theorem _root_.solution [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {n : ℕ} (c : (Fin n → G) → M.V) (hc : Continuous c) :
    ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧
      (∀ (g v : Fin n → G), (∀ i, v i ∈ N) → c (g * v) = c g) ∧
      ∀ g, ∀ a ∈ N, M.rho a (c g) = c g := by
  classical
  obtain ⟨V0, hV0, hV0c⟩ := exists_nhds_right_const c hc
  rw [nhds_pi, Filter.mem_pi] at hV0
  obtain ⟨I, -, t, ht, htV⟩ := hV0
  have hU : (⋂ i, t i) ∈ 𝓝 (1 : G) := Filter.iInter_mem.mpr fun i => ht i
  have hfin : (Set.range c).Finite := (isCompact_range hc).finite_of_discrete
  have hS : (⋂ m ∈ Set.range c, {a : G | M.rho a m = m}) ∈ 𝓝 (1 : G) :=
    (Filter.biInter_mem hfin).mpr fun m _ => stab_mem_nhds M m
  have hW : (⋂ i, t i) ∩ (⋂ m ∈ Set.range c, {a : G | M.rho a m = m}) ∈ 𝓝 (1 : G) :=
    Filter.inter_mem hU hS
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one isOpen_interior
    (mem_interior_iff_mem_nhds.mpr hW)
  refine ⟨H.toOpenSubgroup.toSubgroup, H.isNormal', H.toOpenSubgroup.isOpen', fun g v hv => ?_,
    fun g a ha => ?_⟩
  · apply hV0c g v
    apply htV
    intro i _
    have hvi := interior_subset (hH (hv i))
    exact Set.mem_iInter.mp hvi.1 i
  · have hai := interior_subset (hH ha)
    exact Set.mem_iInter₂.mp hai.2 (c g) ⟨g, rfl⟩
end ReciprocityTheory.Coh.FiniteLevelCohomology
