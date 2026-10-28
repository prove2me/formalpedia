-- Prove2me | solution 1 for RobertsonSeymour1991.GM10.Minimax.result_2_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:08:49.553683+00:00
-- url     : https://prove2.me/submissions/2b4f937d-2c75-42fb-b2c1-5a810af60286

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

open RobertsonSeymour1991.GM10.Minimax in
theorem solution {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) :
    (∃ (θ : ℕ) (𝒯 : Set (G.Sub × G.Sub)), G.IsTangle θ 𝒯) ↔ Nonempty V := by
  constructor
  · rintro ⟨θ, 𝒯, h1, h2, h3, h4, h5⟩
    by_contra hne
    rw [not_nonempty_iff] at hne
    let B : G.Sub := ⟨∅, ∅, fun e he => absurd he (Set.notMem_empty e)⟩
    have hsep : Hypergraph.IsSeparation (Hypergraph.Sub.top G) B := by
      refine ⟨?_, ?_⟩
      · apply Hypergraph.Sub.ext
        · simp [Hypergraph.Sub.union, Hypergraph.Sub.top, B]
        · simp [Hypergraph.Sub.union, Hypergraph.Sub.top, B]
      · simp [Hypergraph.Sub.top, B]
    have hord : Hypergraph.order (Hypergraph.Sub.top G) B < θ := by
      simp [Hypergraph.order, B]; omega
    rcases h3 _ _ hsep hord with h | h
    · exact h5 _ h rfl
    · exact h5 _ h (Set.eq_univ_of_forall (fun x => isEmptyElim x))
  · rintro ⟨v⟩
    refine ⟨1, {p | Hypergraph.IsSeparation p.1 p.2 ∧ Hypergraph.order p.1 p.2 < 1 ∧ v ∈ p.2.verts},
      le_refl 1, fun p hp => ⟨hp.1, hp.2.1⟩, ?_, ?_, ?_⟩
    · intro A B hAB hord
      have hv : v ∈ A.verts ∪ B.verts := by
        have := congrArg Hypergraph.Sub.verts hAB.1
        change A.verts ∪ B.verts = Set.univ at this
        rw [this]; trivial
      rcases hv with hv | hv
      · right
        refine ⟨⟨?_, ?_⟩, ?_, hv⟩
        · apply Hypergraph.Sub.ext
          · have := congrArg Hypergraph.Sub.verts hAB.1
            change A.verts ∪ B.verts = _ at this
            change B.verts ∪ A.verts = _
            rw [Set.union_comm]; exact this
          · have := congrArg Hypergraph.Sub.edges hAB.1
            change A.edges ∪ B.edges = _ at this
            change B.edges ∪ A.edges = _
            rw [Set.union_comm]; exact this
        · rw [Set.inter_comm]; exact hAB.2
        · change (B.verts ∩ A.verts).ncard < 1
          rw [Set.inter_comm]; exact hord
      · left
        exact ⟨hAB, hord, hv⟩
    · intro p₁ hp₁ p₂ hp₂ p₃ hp₃ htop
      have hv : v ∈ ((p₁.1.union p₂.1).union p₃.1).verts := by rw [htop]; trivial
      have key : ∀ p : G.Sub × G.Sub, Hypergraph.order p.1 p.2 < 1 → v ∈ p.2.verts →
          v ∉ p.1.verts := by
        intro p hp hv2 hv1
        have h0 : (p.1.verts ∩ p.2.verts).ncard = 0 := by
          change Hypergraph.order p.1 p.2 = 0; omega
        rw [Set.ncard_eq_zero (Set.toFinite _)] at h0
        have : v ∈ p.1.verts ∩ p.2.verts := ⟨hv1, hv2⟩
        rw [h0] at this; exact this
      change v ∈ (p₁.1.verts ∪ p₂.1.verts) ∪ p₃.1.verts at hv
      rcases hv with (hv | hv) | hv
      · exact key p₁ hp₁.2.1 hp₁.2.2 hv
      · exact key p₂ hp₂.2.1 hp₂.2.2 hv
      · exact key p₃ hp₃.2.1 hp₃.2.2 hv
    · intro p hp huniv
      have h0 : (p.1.verts ∩ p.2.verts).ncard = 0 := by
        have := hp.2.1; change Hypergraph.order p.1 p.2 = 0; omega
      rw [Set.ncard_eq_zero (Set.toFinite _), huniv, Set.univ_inter] at h0
      have := hp.2.2
      rw [h0] at this; exact this
