-- Prove2me | solution 1 for RobertsonSeymour1991.GM10.Minimax.result_2_8_order
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:17:05.141558+00:00
-- url     : https://prove2.me/submissions/042db64f-4228-454f-a250-b581d2634366

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

open RobertsonSeymour1991.GM10.Minimax in
theorem solution {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (A B : G.Sub)
    (hext : Hypergraph.IsExtreme 𝒯 A B) :
    Hypergraph.order A B = θ - 1 := by
  obtain ⟨_, h2, h3, h4, h5⟩ := h𝒯
  obtain ⟨hAB, hmax⟩ := hext
  obtain ⟨hsep, hlt⟩ := h2 _ hAB
  change Hypergraph.order A B < θ at hlt
  change Hypergraph.IsSeparation A B at hsep
  have hv1 : A.verts ∪ B.verts = Set.univ := congrArg Hypergraph.Sub.verts hsep.1
  have he1 : A.edges ∪ B.edges = Set.univ := congrArg Hypergraph.Sub.edges hsep.1
  by_contra hne
  have hlt2 : Hypergraph.order A B + 1 < θ := by omega
  obtain ⟨v, hv⟩ : ∃ v, v ∉ A.verts := by
    by_contra hc
    push_neg at hc
    exact h5 _ hAB (Set.eq_univ_of_forall hc)
  have hvB : v ∈ B.verts := by
    have : v ∈ A.verts ∪ B.verts := by rw [hv1]; trivial
    rcases this with h | h
    · exact absurd h hv
    · exact h
  let A' : G.Sub := ⟨insert v A.verts, A.edges,
    fun e he => (A.ends_subset e he).trans (Set.subset_insert v A.verts)⟩
  have hsep' : Hypergraph.IsSeparation A' B := by
    refine ⟨Hypergraph.Sub.ext ?_ ?_, hsep.2⟩
    · change insert v A.verts ∪ B.verts = Set.univ
      rw [Set.insert_union, hv1, Set.insert_eq_of_mem (Set.mem_univ v)]
    · exact he1
  have hord' : Hypergraph.order A' B = Hypergraph.order A B + 1 := by
    unfold Hypergraph.order
    change (insert v A.verts ∩ B.verts).ncard = _
    rw [Set.insert_inter_of_mem hvB, Set.ncard_insert_of_notMem (fun h => hv h.1)]
  rcases h3 A' B hsep' (by rw [hord']; exact hlt2) with h | h
  · have := (hmax A' B h ⟨Set.subset_insert v A.verts, le_refl _⟩ ⟨le_refl _, le_refl _⟩).1
    have hmem : v ∈ A'.verts := Set.mem_insert v A.verts
    rw [this] at hmem
    exact hv hmem
  · apply h4 _ hAB _ h _ h
    apply Hypergraph.Sub.ext
    · change (A.verts ∪ B.verts) ∪ B.verts = Set.univ
      rw [hv1, Set.univ_union]
    · change (A.edges ∪ B.edges) ∪ B.edges = Set.univ
      rw [he1, Set.univ_union]
