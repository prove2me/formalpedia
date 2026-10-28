-- Prove2me | solution 1 for RobertsonSeymour1991.GM10.Minimax.result_2_8_separation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:16:55.339761+00:00
-- url     : https://prove2.me/submissions/1f9e1426-8c3e-4a06-8b63-a78500582765

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

open RobertsonSeymour1991.GM10.Minimax in
theorem solution {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (A B : G.Sub)
    (hext : Hypergraph.IsExtreme 𝒯 A B) (B₁ B₂ : G.Sub)
    (hunion : B₁.union B₂ = B) (hdisj : B₁.edges ∩ B₂.edges = ∅) :
    (B₁.le (A.inter B) ∧ B₂ = B) ∨ (B₂.le (A.inter B) ∧ B₁ = B) ∨
      min (A.verts ∩ B₁.verts).ncard (A.verts ∩ B₂.verts).ncard < Hypergraph.order B₁ B₂ := by
  obtain ⟨_, h2, h3, h4, _⟩ := h𝒯
  obtain ⟨hAB, hmax⟩ := hext
  obtain ⟨hsep, hlt⟩ := h2 _ hAB
  change Hypergraph.order A B < θ at hlt
  change Hypergraph.IsSeparation A B at hsep
  have hv1 : A.verts ∪ B.verts = Set.univ := congrArg Hypergraph.Sub.verts hsep.1
  have he1 : A.edges ∪ B.edges = Set.univ := congrArg Hypergraph.Sub.edges hsep.1
  have hd1 : A.edges ∩ B.edges = ∅ := hsep.2
  have hBv : B₁.verts ∪ B₂.verts = B.verts := congrArg Hypergraph.Sub.verts hunion
  have hBe : B₁.edges ∪ B₂.edges = B.edges := congrArg Hypergraph.Sub.edges hunion
  have side : ∀ C₁ C₂ : G.Sub, C₁.verts ∪ C₂.verts = B.verts → C₁.edges ∪ C₂.edges = B.edges →
      C₁.edges ∩ C₂.edges = ∅ →
      (C₁.verts ∩ C₂.verts).ncard ≤ (A.verts ∩ C₁.verts).ncard →
      Hypergraph.IsSeparation (A.union C₁) C₂ ∧ Hypergraph.order (A.union C₁) C₂ < θ ∧
        ((A.union C₁, C₂) ∈ 𝒯 → C₁.le (A.inter B) ∧ C₂ = B) := by
    intro C₁ C₂ hCv hCe hCd hcard
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
    · -- inclusion-exclusion
      have hfin : ∀ s : Set V, s.Finite := fun s => Set.toFinite s
      have e1 : (A.verts ∪ C₁.verts) ∩ C₂.verts =
          (A.verts ∩ C₂.verts) ∪ (C₁.verts ∩ C₂.verts) := Set.union_inter_distrib_right _ _ _
      have e2 : (A.verts ∩ C₂.verts) ∩ (C₁.verts ∩ C₂.verts) =
          A.verts ∩ (C₁.verts ∩ C₂.verts) := by
        ext x; simp only [Set.mem_inter_iff]; tauto
      have e3 : A.verts ∩ B.verts = (A.verts ∩ C₁.verts) ∪ (A.verts ∩ C₂.verts) := by
        rw [← hCv, Set.inter_union_distrib_left]
      have e4 : (A.verts ∩ C₁.verts) ∩ (A.verts ∩ C₂.verts) =
          A.verts ∩ (C₁.verts ∩ C₂.verts) := by
        ext x; simp only [Set.mem_inter_iff]; tauto
      have i1 := Set.ncard_union_add_ncard_inter (A.verts ∩ C₂.verts) (C₁.verts ∩ C₂.verts)
        (hfin _) (hfin _)
      have i2 := Set.ncard_union_add_ncard_inter (A.verts ∩ C₁.verts) (A.verts ∩ C₂.verts)
        (hfin _) (hfin _)
      rw [e2] at i1
      rw [e4] at i2
      change ((A.verts ∪ C₁.verts) ∩ C₂.verts).ncard < θ
      unfold Hypergraph.order at hlt
      rw [e3] at hlt
      rw [e1]
      omega
    · intro hmem
      obtain ⟨hA', hC2⟩ := hmax _ _ hmem ⟨Set.subset_union_left, Set.subset_union_left⟩
        ⟨by rw [← hCv]; exact Set.subset_union_right,
         by rw [← hCe]; exact Set.subset_union_right⟩
      have hv : A.verts ∪ C₁.verts = A.verts := congrArg Hypergraph.Sub.verts hA'
      have he : A.edges ∪ C₁.edges = A.edges := congrArg Hypergraph.Sub.edges hA'
      refine ⟨⟨fun x hx => ⟨?_, ?_⟩, fun x hx => ⟨?_, ?_⟩⟩, hC2⟩
      · rw [← hv]; exact Or.inr hx
      · rw [← hCv]; exact Or.inl hx
      · rw [← he]; exact Or.inr hx
      · rw [← hCe]; exact Or.inl hx
  by_cases hlt2 : min (A.verts ∩ B₁.verts).ncard (A.verts ∩ B₂.verts).ncard <
      Hypergraph.order B₁ B₂
  · exact Or.inr (Or.inr hlt2)
  push_neg at hlt2
  rw [le_min_iff] at hlt2
  obtain ⟨c1, c2⟩ := hlt2
  unfold Hypergraph.order at c1 c2
  obtain ⟨s1, o1, m1⟩ := side B₁ B₂ hBv hBe hdisj c1
  obtain ⟨s2, o2, m2⟩ := side B₂ B₁ (by rw [Set.union_comm]; exact hBv)
    (by rw [Set.union_comm]; exact hBe) (by rw [Set.inter_comm]; exact hdisj)
    (by rw [Set.inter_comm]; exact c2)
  rcases h3 _ _ s1 o1 with r1 | r1
  · exact Or.inl (m1 r1)
  rcases h3 _ _ s2 o2 with r2 | r2
  · exact Or.inr (Or.inl (m2 r2))
  exfalso
  apply h4 _ hAB _ r1 _ r2
  apply Hypergraph.Sub.ext
  · change (A.verts ∪ B₂.verts) ∪ B₁.verts = Set.univ
    rw [Set.union_assoc, Set.union_comm B₂.verts, hBv, hv1]
  · change (A.edges ∪ B₂.edges) ∪ B₁.edges = Set.univ
    rw [Set.union_assoc, Set.union_comm B₂.edges, hBe, he1]
