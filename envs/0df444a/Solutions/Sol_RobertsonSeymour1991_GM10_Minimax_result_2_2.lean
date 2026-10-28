-- Prove2me | solution 1 for RobertsonSeymour1991.GM10.Minimax.result_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:13:28.42397+00:00
-- url     : https://prove2.me/submissions/60ca7c8b-c0ad-41ef-8c2f-cb3dc5eb5254

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace Aux_RS_2_2
open RobertsonSeymour1991.GM10.Minimax

lemma union_top_iff {V E : Type} {G : Hypergraph V E} (A B : G.Sub) :
    A.union B = Hypergraph.Sub.top G ↔
      (A.verts ∪ B.verts = Set.univ ∧ A.edges ∪ B.edges = Set.univ) := by
  constructor
  · intro h
    exact ⟨congrArg Hypergraph.Sub.verts h, congrArg Hypergraph.Sub.edges h⟩
  · rintro ⟨h1, h2⟩
    exact Hypergraph.Sub.ext h1 h2

end Aux_RS_2_2

open RobertsonSeymour1991.GM10.Minimax in
theorem solution {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (A B A' B' : G.Sub)
    (hAB : (A, B) ∈ 𝒯) (hA'B' : (A', B') ∈ 𝒯)
    (hord : Hypergraph.order (A.union A') (B.inter B') < θ) :
    (A.union A', B.inter B') ∈ 𝒯 := by
  obtain ⟨_, h2, h3, h4, _⟩ := h𝒯
  obtain ⟨s1, -⟩ := h2 _ hAB
  obtain ⟨s2, -⟩ := h2 _ hA'B'
  obtain ⟨hv1, he1⟩ := (Aux_RS_2_2.union_top_iff A B).mp s1.1
  obtain ⟨hv2, he2⟩ := (Aux_RS_2_2.union_top_iff A' B').mp s2.1
  have hd1 := s1.2
  have hd2 := s2.2
  have hsep : Hypergraph.IsSeparation (A.union A') (B.inter B') := by
    refine ⟨(Aux_RS_2_2.union_top_iff _ _).mpr ⟨?_, ?_⟩, ?_⟩
    · change (A.verts ∪ A'.verts) ∪ (B.verts ∩ B'.verts) = Set.univ
      apply Set.eq_univ_of_forall
      intro v
      have a1 : v ∈ A.verts ∪ B.verts := by rw [hv1]; trivial
      have a2 : v ∈ A'.verts ∪ B'.verts := by rw [hv2]; trivial
      rcases a1 with a1 | a1 <;> rcases a2 with a2 | a2
      · exact Or.inl (Or.inl a1)
      · exact Or.inl (Or.inl a1)
      · exact Or.inl (Or.inr a2)
      · exact Or.inr ⟨a1, a2⟩
    · change (A.edges ∪ A'.edges) ∪ (B.edges ∩ B'.edges) = Set.univ
      apply Set.eq_univ_of_forall
      intro v
      have a1 : v ∈ A.edges ∪ B.edges := by rw [he1]; trivial
      have a2 : v ∈ A'.edges ∪ B'.edges := by rw [he2]; trivial
      rcases a1 with a1 | a1 <;> rcases a2 with a2 | a2
      · exact Or.inl (Or.inl a1)
      · exact Or.inl (Or.inl a1)
      · exact Or.inl (Or.inr a2)
      · exact Or.inr ⟨a1, a2⟩
    · change (A.edges ∪ A'.edges) ∩ (B.edges ∩ B'.edges) = ∅
      apply Set.eq_empty_of_forall_notMem
      rintro x ⟨hx | hx, hb, hb'⟩
      · have : x ∈ A.edges ∩ B.edges := ⟨hx, hb⟩
        rw [hd1] at this; exact this
      · have : x ∈ A'.edges ∩ B'.edges := ⟨hx, hb'⟩
        rw [hd2] at this; exact this
  rcases h3 _ _ hsep hord with h | h
  · exact h
  · exfalso
    apply h4 _ hAB _ hA'B' _ h
    exact (Aux_RS_2_2.union_top_iff _ _).mpr ⟨(Aux_RS_2_2.union_top_iff _ _).mp hsep.1 |>.1,
      (Aux_RS_2_2.union_top_iff _ _).mp hsep.1 |>.2⟩
