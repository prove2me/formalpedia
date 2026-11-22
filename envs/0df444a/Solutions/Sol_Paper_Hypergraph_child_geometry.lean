-- Prove2me | solution 1 for Paper.Hypergraph.child_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:57.669802+00:00
-- url     : https://prove2.me/submissions/7df3f606-4377-438c-ad9d-1e246eb76e52

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {W B K : Finset ℕ}
    (hBW : B ⊆ W) (hK : K ∈ (H.induce (W \ B)).components) :
    (K ∪ (H.induce W).boundary B K) ⊆ W ∧
    (K ∪ (H.induce W).boundary B K) \ (H.induce W).boundary B K = K ∧
    (K ∪ (H.induce W).boundary B K) ∩ B = (H.induce W).boundary B K := by
  have hsub : K ⊆ W \ B := fun v hv =>
    (mem_inter.mp (mem_powerset.mp (mem_filter.mp hK).1 hv)).2
  have hbd : (H.induce W).boundary B K ⊆ B := filter_subset _ _
  refine ⟨union_subset (hsub.trans sdiff_subset) (hbd.trans hBW), ?_, ?_⟩
  · ext v
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hv | hv, hn⟩
      · exact hv
      · exact (hn hv).elim
    · intro hv
      exact ⟨Or.inl hv, fun hb => (mem_sdiff.mp (hsub hv)).2 (hbd hb)⟩
  · ext v
    simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨hv | hv, hb⟩
      · exact ((mem_sdiff.mp (hsub hv)).2 hb).elim
      · exact hv
    · intro hv
      exact ⟨Or.inr hv, hbd hv⟩
end Paper.Hypergraph
