-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.exists_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:10.257647+00:00
-- url     : https://prove2.me/submissions/edb2a3b0-d449-45bf-b4a5-480058411b83

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_normal_of_comm
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_index_pos
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_mem_zpowers_quot
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_zpow_mem_iff

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
theorem _root_.solution [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (g : G) :
    ∃ j : ℕ, g⁻¹ * s ^ j ∈ W := by
  haveI := normal_of_comm hc W
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_quot hs hW (g : G ⧸ W))
  rw [← map_zpow, QuotientGroup.mk'_apply] at hk
  have hgk : g⁻¹ * s ^ k ∈ W := QuotientGroup.eq.mp hk.symm
  have hn : (0 : ℤ) < W.index := by exact_mod_cast index_pos hc hW
  refine ⟨(k % (W.index : ℤ)).toNat, ?_⟩
  have hj : (((k % (W.index : ℤ)).toNat : ℕ) : ℤ) = k % (W.index : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hn.ne')
  have hd : s ^ (k % (W.index : ℤ) - k) ∈ W := by
    rw [zpow_mem_iff hc hs hW]
    exact ⟨-(k / (W.index : ℤ)), by rw [Int.emod_def]; ring⟩
  have heq : g⁻¹ * s ^ (k % (W.index : ℤ)).toNat =
      (g⁻¹ * s ^ k) * s ^ (k % (W.index : ℤ) - k) := by
    rw [mul_assoc, ← zpow_add, ← zpow_natCast, hj]
    congr 2
    ring
  rw [heq]
  exact W.mul_mem hgk hd
end ReciprocityTheory.Coh.ProcyclicCohomology
