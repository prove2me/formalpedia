-- Prove2me | solution 1 for ReciprocityTheory.Coh.ContinuousSections.adm_of_section_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:50.16672+00:00
-- url     : https://prove2.me/submissions/d60f8eef-c3e3-43f8-91d3-3ba3fb31f73f

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Definitions.Def_ReciprocityTheory_GroupCohomology_SectionA
import Theorems.Thm_ReciprocityTheory_Coh_ContinuousSections_rep_eq
import Theorems.Thm_ReciprocityTheory_Coh_ContinuousSections_rep_spec
import Theorems.Thm_ReciprocityTheory_Coh_ContinuousSections_tr_coset
import Theorems.Thm_ReciprocityTheory_Coh_ContinuousSections_tr_closed

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
theorem _root_.solution (U K : Subgroup G) (S : Set G) (h : admitted U (K, S)) (N : Subgroup G) [N.Normal]
    (hN : IsOpen (N : Set G)) : admitted U (K ⊓ N, S ∩ tr K N) := by
  obtain ⟨hKU, hSc, hKS, hSK, hSU⟩ := h
  refine ⟨inf_le_left.trans hKU, hSc.inter (tr_closed K N hN), ?_, ?_, ?_⟩
  · rintro k ⟨hkK, hkN⟩ s ⟨hsS, hsT⟩
    refine ⟨hKS k hkK s hsS, (tr_coset K N ?_).2 hsT⟩
    simpa using hkN
  · rintro a ⟨haS, haT⟩ b ⟨hbS, hbT⟩ hab
    have habK := hSK a haS b hbS hab
    refine ⟨habK, ?_⟩
    have hr : rep K N b = rep K N a := rep_eq K N ⟨a * b⁻¹, habK, 1, N.one_mem, by group⟩
    have ha : a * (rep K N a)⁻¹ ∈ N := haT
    have hb : b * (rep K N b)⁻¹ ∈ N := hbT
    rw [hr] at hb
    have := N.mul_mem ha (N.inv_mem hb)
    simpa [mul_assoc] using this
  · intro g
    obtain ⟨a, haS, hag⟩ := hSU g
    obtain ⟨k, hk, n, hn, ha⟩ := rep_spec K N a
    set r := rep K N a with hrdef
    have hrel : rep K N (k⁻¹ * a) = r := (rep_eq K N ⟨k⁻¹, K.inv_mem hk, 1, N.one_mem, by group⟩).symm
    refine ⟨k⁻¹ * a, ⟨hKS _ (K.inv_mem hk) a haS, ?_⟩, ?_⟩
    · show k⁻¹ * a * (rep K N (k⁻¹ * a))⁻¹ ∈ N
      rw [hrel, ha]
      simpa [mul_assoc] using hn
    · rw [mul_assoc]
      exact U.mul_mem (U.inv_mem (hKU hk)) hag
end ReciprocityTheory.Coh.ContinuousSections
