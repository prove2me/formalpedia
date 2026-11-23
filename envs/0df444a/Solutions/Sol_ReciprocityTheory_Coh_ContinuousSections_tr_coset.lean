-- Prove2me | solution 1 for ReciprocityTheory.Coh.ContinuousSections.tr_coset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:29.81155+00:00
-- url     : https://prove2.me/submissions/54a6e808-8967-451d-b895-c1be611e47ca

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Definitions.Def_ReciprocityTheory_GroupCohomology_SectionA
import Theorems.Thm_ReciprocityTheory_Coh_ContinuousSections_rep_eq

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
namespace ReciprocityTheory.Coh.ContinuousSections
theorem _root_.solution (K N : Subgroup G) [N.Normal] {y z : G} (h : z * y⁻¹ ∈ N) :
    z ∈ tr K N ↔ y ∈ tr K N := by
  have hr : rep K N z = rep K N y :=
    (rep_eq K N ⟨1, K.one_mem, z * y⁻¹, h, by group⟩).symm
  show z * (rep K N z)⁻¹ ∈ N ↔ y * (rep K N y)⁻¹ ∈ N
  rw [hr, show z * (rep K N y)⁻¹ = z * y⁻¹ * (y * (rep K N y)⁻¹) by group]
  exact N.mul_mem_cancel_left h
end ReciprocityTheory.Coh.ContinuousSections
