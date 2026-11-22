-- Prove2me | solution 1 for Paper.Hypergraph.edgeDistance_indicator_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:51.460035+00:00
-- url     : https://prove2.me/submissions/5237e5e0-b784-47af-808b-6a64f9d0d27f

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_primal_induce_adj
import Theorems.Thm_Paper_Hypergraph_edgeDistance_indicator
import Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (S : Finset ℕ)
    {e f u : ℕ} (he : e ∈ H.edges) (hf : f ∈ H.edges) (hue : u ∈ H.edge e)
    {K : Finset ℕ} (hK : K ∈ (H.induce (H.vertices \ S)).components) (huK : u ∈ K) :
    H.edgeDistance (indicator S) e f = if ¬ Disjoint (H.edge f) K then 0 else 1 := by
  have hsub : K ⊆ (H.induce (H.vertices \ S)).vertices :=
    mem_powerset.mp (mem_filter.mp hK).1
  have huW := (mem_inter.mp (hsub huK)).2
  have hiff : (∃ a ∈ H.edge e, ∃ b ∈ H.edge f,
      a ∉ S ∧ b ∉ S ∧ (H.induce (H.vertices \ S)).primal.Reachable a b) ↔
      ¬ Disjoint (H.edge f) K := by
    constructor
    · rintro ⟨a, hae, b, hbf, haS, hbS, hab⟩
      have haW : a ∈ H.vertices \ S := mem_sdiff.mpr ⟨H.edge_subset e he hae, haS⟩
      have hua : (H.induce (H.vertices \ S)).primal.Reachable u a := by
        by_cases h : u = a
        · subst a; exact .rfl
        · exact ((H.primal_induce_adj _ huW haW).mpr ⟨h, e, he, hue, hae⟩).reachable
      have hbV := H.edge_subset f hf hbf
      have hbJ : b ∈ (H.induce (H.vertices \ S)).vertices :=
        mem_inter.mpr ⟨hbV, mem_sdiff.mpr ⟨hbV, hbS⟩⟩
      have hbK := ((H.induce (H.vertices \ S)).component_mem_iff_reachable hK huK hbJ).mpr
        (hua.trans hab)
      exact not_disjoint_iff.mpr ⟨b, hbf, hbK⟩
    · intro hmeet
      obtain ⟨b, hbf, hbK⟩ := not_disjoint_iff.mp hmeet
      have hbJ := hsub hbK
      exact ⟨u, hue, b, hbf, (mem_sdiff.mp huW).2,
        (mem_sdiff.mp (mem_inter.mp hbJ).2).2,
        ((H.induce (H.vertices \ S)).component_mem_iff_reachable hK huK hbJ).mp hbK⟩
  rw [H.edgeDistance_indicator S he hf]
  simp only [hiff]
end Paper.Hypergraph
