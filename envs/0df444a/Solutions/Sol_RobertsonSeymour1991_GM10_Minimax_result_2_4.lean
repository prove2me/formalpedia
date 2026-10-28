-- Prove2me | solution 1 for RobertsonSeymour1991.GM10.Minimax.result_2_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:11:06.837078+00:00
-- url     : https://prove2.me/submissions/0f111fe7-edb2-4bae-885e-4b3f99fa18c4

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace Aux_RS_2_4
open RobertsonSeymour1991.GM10.Minimax

lemma sep_symm {V E : Type} {G : Hypergraph V E} {A B : G.Sub}
    (h : Hypergraph.IsSeparation A B) : Hypergraph.IsSeparation B A := by
  refine ⟨?_, ?_⟩
  · apply Hypergraph.Sub.ext
    · have := congrArg Hypergraph.Sub.verts h.1
      change A.verts ∪ B.verts = _ at this
      change B.verts ∪ A.verts = _
      rw [Set.union_comm]; exact this
    · have := congrArg Hypergraph.Sub.edges h.1
      change A.edges ∪ B.edges = _ at this
      change B.edges ∪ A.edges = _
      rw [Set.union_comm]; exact this
  · rw [Set.inter_comm]; exact h.2

lemma order_symm {V E : Type} {G : Hypergraph V E} (A B : G.Sub) :
    Hypergraph.order A B = Hypergraph.order B A := by
  unfold Hypergraph.order; rw [Set.inter_comm]

end Aux_RS_2_4

open RobertsonSeymour1991.GM10.Minimax in
theorem solution {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ) (hθ : 1 ≤ θ)
    (e : E) (he : θ ≤ G.size e) :
    G.IsTangle θ {p : G.Sub × G.Sub |
      Hypergraph.IsSeparation p.1 p.2 ∧ Hypergraph.order p.1 p.2 < θ ∧ e ∈ p.2.edges} := by
  refine ⟨hθ, fun p hp => ⟨hp.1, hp.2.1⟩, ?_, ?_, ?_⟩
  · intro A B hAB hord
    have hv : e ∈ A.edges ∪ B.edges := by
      have := congrArg Hypergraph.Sub.edges hAB.1
      change A.edges ∪ B.edges = Set.univ at this
      rw [this]; trivial
    rcases hv with hv | hv
    · right
      exact ⟨Aux_RS_2_4.sep_symm hAB, by rw [Aux_RS_2_4.order_symm]; exact hord, hv⟩
    · left
      exact ⟨hAB, hord, hv⟩
  · intro p₁ hp₁ p₂ hp₂ p₃ hp₃ htop
    have hv : e ∈ ((p₁.1.union p₂.1).union p₃.1).edges := by rw [htop]; trivial
    have key : ∀ p : G.Sub × G.Sub, Hypergraph.IsSeparation p.1 p.2 → e ∈ p.2.edges →
        e ∉ p.1.edges := by
      intro p hp hv2 hv1
      have : e ∈ p.1.edges ∩ p.2.edges := ⟨hv1, hv2⟩
      rw [hp.2] at this; exact this
    change e ∈ (p₁.1.edges ∪ p₂.1.edges) ∪ p₃.1.edges at hv
    rcases hv with (hv | hv) | hv
    · exact key p₁ hp₁.1 hp₁.2.2 hv
    · exact key p₂ hp₂.1 hp₂.2.2 hv
    · exact key p₃ hp₃.1 hp₃.2.2 hv
  · intro p hp huniv
    have h1 : Hypergraph.order p.1 p.2 = p.2.verts.ncard := by
      unfold Hypergraph.order; rw [huniv, Set.univ_inter]
    have h2 : G.size e ≤ p.2.verts.ncard :=
      Set.ncard_le_ncard (p.2.ends_subset e hp.2.2) (Set.toFinite _)
    have := hp.2.1
    omega
