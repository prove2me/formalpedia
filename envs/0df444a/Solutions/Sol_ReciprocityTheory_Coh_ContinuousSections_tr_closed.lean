-- Prove2me | solution 1 for ReciprocityTheory.Coh.ContinuousSections.tr_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:51:53.185087+00:00
-- url     : https://prove2.me/submissions/7012d995-bfa1-4325-98c2-8dcd26580864

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Definitions.Def_ReciprocityTheory_GroupCohomology_SectionA
import Theorems.Thm_ReciprocityTheory_Coh_ContinuousSections_tr_coset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise Set
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.ContinuousSections
variable {G : Type*} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.ContinuousSections
theorem _root_.solution (K N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G)) : IsClosed (tr K N) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  refine ⟨(fun z => z * y⁻¹) ⁻¹' (N : Set G), fun z hz hzt => hy ((tr_coset K N hz).1 hzt),
    hN.preimage (continuous_id.mul continuous_const), ?_⟩
  simp
end ReciprocityTheory.Coh.ContinuousSections
