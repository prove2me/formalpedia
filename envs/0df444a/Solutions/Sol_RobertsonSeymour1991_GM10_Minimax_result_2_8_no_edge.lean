-- Prove2me | solution 1 for RobertsonSeymour1991.GM10.Minimax.result_2_8_no_edge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:21:49.852308+00:00
-- url     : https://prove2.me/submissions/07cc77cc-0a04-4203-94b0-38fe4f0cd52e

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

open RobertsonSeymour1991.GM10.Minimax in
theorem solution {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (A B : G.Sub)
    (hext : Hypergraph.IsExtreme 𝒯 A B) :
    ∀ e ∈ B.edges, ¬ G.ends e ⊆ A.verts := by
  obtain ⟨_, h2, h3, h4, h5⟩ := h𝒯
  obtain ⟨hAB, hmax⟩ := hext
  obtain ⟨hsep, hlt⟩ := h2 _ hAB
  change Hypergraph.order A B < θ at hlt
  change Hypergraph.IsSeparation A B at hsep
  have hv1 : A.verts ∪ B.verts = Set.univ := congrArg Hypergraph.Sub.verts hsep.1
  have he1 : A.edges ∪ B.edges = Set.univ := congrArg Hypergraph.Sub.edges hsep.1
  have hd1 : A.edges ∩ B.edges = ∅ := hsep.2
  intro e he hsub
  have heA : e ∉ A.edges := by
    intro h
    have : e ∈ A.edges ∩ B.edges := ⟨h, he⟩
    rw [hd1] at this; exact this
  have hendsB : G.ends e ⊆ B.verts := B.ends_subset e he
  have hcard : (G.ends e).ncard ≤ Hypergraph.order A B :=
    Set.ncard_le_ncard (fun x hx => ⟨hsub hx, hendsB hx⟩) (Set.toFinite _)
  -- the separation (edgeSub e, deleteEdges {e})
  have hsepE : Hypergraph.IsSeparation (G.edgeSub e) (G.deleteEdges {e}) := by
    refine ⟨Hypergraph.Sub.ext ?_ ?_, ?_⟩
    · change G.ends e ∪ Set.univ = Set.univ
      exact Set.union_univ _
    · change {e} ∪ ({e} : Set E)ᶜ = Set.univ
      exact Set.union_compl_self _
    · change {e} ∩ ({e} : Set E)ᶜ = ∅
      exact Set.inter_compl_self _
  have hordE : Hypergraph.order (G.edgeSub e) (G.deleteEdges {e}) < θ := by
    change (G.ends e ∩ Set.univ).ncard < θ
    rw [Set.inter_univ]; omega
  have hE : (G.edgeSub e, G.deleteEdges {e}) ∈ 𝒯 := by
    rcases h3 _ _ hsepE hordE with h | h
    · exact h
    · exact absurd rfl (h5 _ h)
  let A' : G.Sub := ⟨A.verts, insert e A.edges, by
    intro f hf
    rcases hf with hf | hf
    · rw [hf]; exact hsub
    · exact A.ends_subset f hf⟩
  let B' : G.Sub := ⟨B.verts, B.edges \ {e}, fun f hf => B.ends_subset f hf.1⟩
  have hsep' : Hypergraph.IsSeparation A' B' := by
    refine ⟨Hypergraph.Sub.ext hv1 ?_, ?_⟩
    · change insert e A.edges ∪ (B.edges \ {e}) = Set.univ
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x = e
      · exact Or.inl (Or.inl hx)
      · have : x ∈ A.edges ∪ B.edges := by rw [he1]; trivial
        rcases this with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨h, hx⟩
    · change insert e A.edges ∩ (B.edges \ {e}) = ∅
      apply Set.eq_empty_of_forall_notMem
      rintro x ⟨hx | hx, hxB, hxe⟩
      · exact hxe hx
      · have : x ∈ A.edges ∩ B.edges := ⟨hx, hxB⟩
        rw [hd1] at this; exact this
  have hord' : Hypergraph.order A' B' < θ := hlt
  rcases h3 _ _ hsep' hord' with h | h
  · have heq := (hmax _ _ h ⟨le_refl _, Set.subset_insert e A.edges⟩
      ⟨le_refl _, Set.diff_subset⟩).1
    have : e ∈ A'.edges := Set.mem_insert e A.edges
    rw [heq] at this
    exact heA this
  · apply h4 _ hAB _ h _ hE
    apply Hypergraph.Sub.ext
    · change (A.verts ∪ B.verts) ∪ G.ends e = Set.univ
      rw [hv1, Set.univ_union]
    · change (A.edges ∪ (B.edges \ {e})) ∪ {e} = Set.univ
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x = e
      · exact Or.inr hx
      · have : x ∈ A.edges ∪ B.edges := by rw [he1]; trivial
        rcases this with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨h, hx⟩)
