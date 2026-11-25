-- Prove2me | solution 1 for ReciprocityTheory.Coh.ContinuousSections.admissible_chain_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:46.757798+00:00
-- url     : https://prove2.me/submissions/42605ec6-e499-414c-890d-d71348c6f441

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Definitions.Def_ReciprocityTheory_GroupCohomology_SectionA

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.ContinuousSections
theorem _root_.solution [CompactSpace G] (U : Subgroup G) (hU : IsClosed (U : Set G))
    (c : Set (Subgroup G × Set G)) (hc : ∀ p ∈ c, admitted U p)
    (htot : ∀ p ∈ c, ∀ q ∈ c, p ≤ q ∨ q ≤ p) (y : Subgroup G × Set G) (hy : y ∈ c) :
    admitted U (⨅ p ∈ c, p.1, ⋂ p ∈ c, p.2) := by
  refine ⟨(iInf₂_le y hy).trans (hc y hy).1, isClosed_biInter fun p hp => (hc p hp).2.1, ?_, ?_, ?_⟩
  · intro k hk s hs
    simp only [Subgroup.mem_iInf] at hk
    simp only [Set.mem_iInter] at hs ⊢
    exact fun p hp => (hc p hp).2.2.1 k (hk p hp) s (hs p hp)
  · intro a ha b hb hab
    simp only [Set.mem_iInter] at ha hb
    simp only [Subgroup.mem_iInf]
    exact fun p hp => (hc p hp).2.2.2.1 a (ha p hp) b (hb p hp) hab
  · intro g
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    have hne := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun p : c => p.1.2 ∩ {a | a * g⁻¹ ∈ U}) ?_ ?_
      (fun p => ((hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul continuous_const))).isCompact)
      (fun p => (hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul continuous_const)))
    · obtain ⟨a, ha⟩ := hne
      simp only [Set.mem_iInter] at ha
      refine ⟨a, ?_, (ha ⟨y, hy⟩).2⟩
      simp only [Set.mem_iInter]
      exact fun p hp => (ha ⟨p, hp⟩).1
    · intro p q
      rcases htot p.1 p.2 q.1 q.2 with hpq | hqp
      · exact ⟨p, le_rfl, Set.inter_subset_inter_left _ (Prod.le_def.1 hpq).2⟩
      · exact ⟨q, Set.inter_subset_inter_left _ (Prod.le_def.1 hqp).2, le_rfl⟩
    · intro p
      obtain ⟨a, haS, hag⟩ := (hc p.1 p.2).2.2.2.2 g
      exact ⟨a, haS, hag⟩
end ReciprocityTheory.Coh.ContinuousSections
