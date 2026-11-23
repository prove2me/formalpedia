-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.zpow_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:32.61631+00:00
-- url     : https://prove2.me/submissions/7a19d81a-7b5c-4f40-9780-04e79fa90b37

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_normal_of_comm
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_finite_quot
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_mem_zpowers_quot

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
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (z : ℤ) :
    s ^ z ∈ W ↔ (W.index : ℤ) ∣ z := by
  haveI := normal_of_comm hc W
  haveI := finite_quot hc hW
  have hord : orderOf (QuotientGroup.mk' W s) = W.index := by
    rw [orderOf_eq_card_of_forall_mem_zpowers (mem_zpowers_quot hs hW)]
    rfl
  rw [← QuotientGroup.eq_one_iff (N := W), ← hord, orderOf_dvd_iff_zpow_eq_one, ← map_zpow,
    QuotientGroup.mk'_apply]
end ReciprocityTheory.Coh.ProcyclicCohomology
