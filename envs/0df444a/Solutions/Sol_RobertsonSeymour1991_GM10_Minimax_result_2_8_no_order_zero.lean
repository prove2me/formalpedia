-- Prove2me | solution 1 for RobertsonSeymour1991.GM10.Minimax.result_2_8_no_order_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:19:38.622002+00:00
-- url     : https://prove2.me/submissions/afe33a2d-b579-446f-954e-82a5e0467472

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

open RobertsonSeymour1991.GM10.Minimax in
theorem solution {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (A B : G.Sub)
    (hext : Hypergraph.IsExtreme 𝒯 A B) :
    ¬ ∃ B₁ B₂ : G.Sub, B₁.union B₂ = B ∧ B₁.edges ∩ B₂.edges = ∅ ∧
      B₁.verts.Nonempty ∧ B₂.verts.Nonempty ∧ Hypergraph.order B₁ B₂ = 0 := by
  obtain ⟨_, h2, h3, h4, _⟩ := h𝒯
  obtain ⟨hAB, hmax⟩ := hext
  obtain ⟨hsep, hlt⟩ := h2 _ hAB
  change Hypergraph.order A B < θ at hlt
  change Hypergraph.IsSeparation A B at hsep
  have hv1 : A.verts ∪ B.verts = Set.univ := congrArg Hypergraph.Sub.verts hsep.1
  have he1 : A.edges ∪ B.edges = Set.univ := congrArg Hypergraph.Sub.edges hsep.1
  have hd1 : A.edges ∩ B.edges = ∅ := hsep.2
  rintro ⟨B₁, B₂, hU, hd, hn1, hn2, h0⟩
  have hBv : B₁.verts ∪ B₂.verts = B.verts := congrArg Hypergraph.Sub.verts hU
  have hBe : B₁.edges ∪ B₂.edges = B.edges := congrArg Hypergraph.Sub.edges hU
  have hvd : B₁.verts ∩ B₂.verts = ∅ := by
    unfold Hypergraph.order at h0
    exact (Set.ncard_eq_zero (Set.toFinite _)).mp h0
  have side : ∀ C₁ C₂ : G.Sub, C₁.verts ∪ C₂.verts = B.verts → C₁.edges ∪ C₂.edges = B.edges →
      C₁.edges ∩ C₂.edges = ∅ → C₁.verts.Nonempty → C₁.verts ∩ C₂.verts = ∅ →
      Hypergraph.IsSeparation (A.union C₁) C₂ ∧ Hypergraph.order (A.union C₁) C₂ < θ ∧
        (A.union C₁, C₂) ∉ 𝒯 := by
    intro C₁ C₂ hCv hCe hCd hCn hCvd
    refine ⟨⟨Hypergraph.Sub.ext ?_ ?_, ?_⟩, ?_, ?_⟩
    · change (A.verts ∪ C₁.verts) ∪ C₂.verts = Set.univ
      rw [Set.union_assoc, hCv, hv1]
    · change (A.edges ∪ C₁.edges) ∪ C₂.edges = Set.univ
      rw [Set.union_assoc, hCe, he1]
    · change (A.edges ∪ C₁.edges) ∩ C₂.edges = ∅
      apply Set.eq_empty_of_forall_notMem
      rintro x ⟨hx | hx, hx2⟩
      · have : x ∈ A.edges ∩ B.edges := ⟨hx, by rw [← hCe]; exact Or.inr hx2⟩
        rw [hd1] at this; exact this
      · have : x ∈ C₁.edges ∩ C₂.edges := ⟨hx, hx2⟩
        rw [hCd] at this; exact this
    · have hsub : (A.verts ∪ C₁.verts) ∩ C₂.verts ⊆ A.verts ∩ B.verts := by
        rintro x ⟨hx | hx, hx2⟩
        · exact ⟨hx, by rw [← hCv]; exact Or.inr hx2⟩
        · have : x ∈ C₁.verts ∩ C₂.verts := ⟨hx, hx2⟩
          rw [hCvd] at this; exact this.elim
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      change ((A.verts ∪ C₁.verts) ∩ C₂.verts).ncard < θ
      unfold Hypergraph.order at hlt
      omega
    · intro hmem
      have heq := (hmax _ _ hmem ⟨Set.subset_union_left, Set.subset_union_left⟩
        ⟨by rw [← hCv]; exact Set.subset_union_right,
         by rw [← hCe]; exact Set.subset_union_right⟩).2
      obtain ⟨x, hx⟩ := hCn
      have hxB : x ∈ C₂.verts := by rw [heq, ← hCv]; exact Or.inl hx
      have : x ∈ C₁.verts ∩ C₂.verts := ⟨hx, hxB⟩
      rw [hCvd] at this; exact this
  obtain ⟨s1, o1, n1⟩ := side B₁ B₂ hBv hBe hd hn1 hvd
  obtain ⟨s2, o2, n2⟩ := side B₂ B₁ (by rw [Set.union_comm]; exact hBv)
    (by rw [Set.union_comm]; exact hBe) (by rw [Set.inter_comm]; exact hd) hn2
    (by rw [Set.inter_comm]; exact hvd)
  have r1 : (B₂, A.union B₁) ∈ 𝒯 := (h3 _ _ s1 o1).resolve_left n1
  have r2 : (B₁, A.union B₂) ∈ 𝒯 := (h3 _ _ s2 o2).resolve_left n2
  apply h4 _ hAB _ r1 _ r2
  apply Hypergraph.Sub.ext
  · change (A.verts ∪ B₂.verts) ∪ B₁.verts = Set.univ
    rw [Set.union_assoc, Set.union_comm B₂.verts, hBv, hv1]
  · change (A.edges ∪ B₂.edges) ∪ B₁.edges = Set.univ
    rw [Set.union_assoc, Set.union_comm B₂.edges, hBe, he1]
