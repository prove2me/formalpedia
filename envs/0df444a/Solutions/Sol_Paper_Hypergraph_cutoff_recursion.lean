-- Prove2me | solution 1 for Paper.Hypergraph.cutoff_recursion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:42.377035+00:00
-- url     : https://prove2.me/submissions/5f2d6a72-e6af-47ed-8343-5d974c7b8f05

import Definitions.Def_Paper_RoundingCutoff
import Definitions.Def_Paper_RoundingRecursion
import Theorems.Thm_Paper_Hypergraph_component_subset_of_edge_partition
import Theorems.Thm_Paper_Hypergraph_component_contained_in_induced_component
import Theorems.Thm_Paper_Hypergraph_edgeVolume_mono
import Theorems.Thm_Paper_Hypergraph_restrictDemand_cost_mono
import Theorems.Thm_Paper_Hypergraph_separated_restrictDemand_cost_add_le
import Theorems.Thm_Paper_Hypergraph_setCoverCost_union_le


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ x : ℕ → ℝ} {V C : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hC : 0 ≤ C)
    (Q : Finset ℕ) (hQ : Q ⊆ H.vertices)
    (hcut : ∀ U ⊆ Q, U.Nonempty → Nonempty (H.CutoffPiece γ x U V C)) :
    ∃ S ⊆ Q, S ⊆ H.vertices.filter (fun v => x v ≠ 0) ∧
      (∀ K ∈ (H.induce (Q \ S)).components, H.edgeVolume γ K ≤ V) ∧
      H.setCoverCost S ≤ C * H.coverCost (restrictDemand x Q) := by
  revert hQ hcut
  induction Q using Finset.strongInductionOn with
  | _ Q ih =>
    intro hQ hcut
    by_cases hne : Q.Nonempty
    swap
    · have hQ0 := Finset.not_nonempty_iff_eq_empty.mp hne
      subst Q
      refine ⟨∅, empty_subset _, empty_subset _, ?_, ?_⟩
      · intro K hK
        simp [components, induce] at hK
        rcases hK with ⟨rfl, v, hv⟩
        simp at hv
      · have hz : H.setCoverCost ∅ = 0 := H.coverCost_eq_zero_of_nonpos
          (fun v hv => by simp [indicator])
        rw [hz]
        exact mul_nonneg hC (H.coverCost_nonneg _)
    obtain ⟨cut⟩ := hcut Q (Subset.refl _) hne
    let U := Q \ (cut.piece ∪ cut.separator)
    have hUQ : U ⊆ Q := sdiff_subset
    have hproper : U ⊂ Q := by
      apply Finset.ssubset_iff_subset_ne.mpr ⟨hUQ, ?_⟩
      intro heq
      obtain ⟨v, hv⟩ := cut.nonempty
      have hvU : v ∈ U := heq.symm ▸ cut.piece_subset hv
      exact (mem_sdiff.mp hvU).2 (mem_union_left _ hv)
    obtain ⟨S, hSU, hSsupp, hSbal, hScost⟩ := ih U hproper (hUQ.trans hQ)
      (fun T hTU hT => hcut T (hTU.trans hUQ) hT)
    refine ⟨cut.separator ∪ S, union_subset cut.separator_subset (hSU.trans hUQ),
      union_subset cut.support hSsupp, ?_, ?_⟩
    · intro K hK
      have hcover : Q \ (cut.separator ∪ S) ⊆ cut.piece ∪ (U \ S) := by
        intro v hv
        obtain ⟨hvQ, hvout⟩ := mem_sdiff.mp hv
        by_cases hvP : v ∈ cut.piece
        · exact mem_union_left _ hvP
        · apply mem_union_right
          apply mem_sdiff.mpr
          refine ⟨mem_sdiff.mpr ⟨hvQ, ?_⟩, ?_⟩
          · intro hv
            rcases mem_union.mp hv with h | h
            · exact hvP h
            · exact hvout (mem_union_left _ h)
          · intro h
            exact hvout (mem_union_right _ h)
      have hsep : ∀ e ∈ H.edges, Disjoint (H.edge e) cut.piece ∨ Disjoint (H.edge e) (U \ S) := by
        intro e he
        rcases cut.separated e he with h | h
        · exact Or.inl h
        · exact Or.inr (h.mono_right sdiff_subset)
      rcases H.component_subset_of_edge_partition hcover hsep hK with hKP | hKT
      · exact (H.edgeVolume_mono hγ hKP).trans cut.volume_le
      · obtain ⟨L, hL, hKL⟩ := H.component_contained_in_induced_component hK hKT
        exact (H.edgeVolume_mono hγ hKL).trans (hSbal L hL)
    · have hsum : H.coverCost (restrictDemand x cut.piece) + H.coverCost (restrictDemand x U) ≤
          H.coverCost (restrictDemand x Q) := by
        apply (H.separated_restrictDemand_cost_add_le x cut.piece U cut.separated).trans
        exact H.restrictDemand_cost_mono hx (union_subset cut.piece_subset hUQ)
      calc
        _ ≤ H.setCoverCost cut.separator + H.setCoverCost S := H.setCoverCost_union_le _ _
        _ ≤ C * H.coverCost (restrictDemand x cut.piece) + C * H.coverCost (restrictDemand x U) :=
          add_le_add cut.cost_le hScost
        _ = C * (H.coverCost (restrictDemand x cut.piece) + H.coverCost (restrictDemand x U)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC
end Paper.Hypergraph
