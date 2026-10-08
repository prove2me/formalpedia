-- Prove2me | solution 1 for PlaneDrawingSelectedEdgeAwayFromEndpointCompact
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T17:13:42.422971+00:00
-- url     : https://prove2.me/submissions/3dcdef79-51e2-4dc4-a84a-9383fdeffd74

import Mathlib
import Definitions.Def_OrdinaryDrawingImageWithoutEdge
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PolygonalArc

set_option autoImplicit false

open Classical in
theorem PolygonalArc.isCompact_carrier_3f48 (γ : PolygonalArc) : IsCompact γ.carrier := by
  rw [γ.carrier_eq]
  have hs : {p | ∃ i : ℕ, ∃ hi : i + 1 < γ.vertices.length,
      p ∈ segment ℝ γ.vertices[i] γ.vertices[i + 1]} =
      ⋃ i ∈ Finset.range γ.vertices.length, ⋃ (hi : i + 1 < γ.vertices.length),
        segment ℝ γ.vertices[i] γ.vertices[i + 1] := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, hp⟩; exact ⟨i, by omega, hi, hp⟩
    · rintro ⟨i, _, hi, hp⟩; exact ⟨i, hi, hp⟩
  rw [hs]
  refine (Finset.range _).isCompact_biUnion fun i _ => isCompact_iUnion fun hi => ?_
  rw [← convexHull_pair (𝕜 := ℝ)]
  exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.toFinite _)

open Classical in
theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (e : G.edgeFinset) (γ : PolygonalArc) :
    D.edgeArc e = γ →
      ∀ r₀ r₁ : ℝ, 0 < r₀ → 0 < r₁ →
        let A : Set (EuclideanSpace ℝ (Fin 2)) :=
          OrdinaryDrawingImageWithoutEdge G D e \
            (Metric.ball γ.source r₀ ∪ Metric.ball γ.target r₁)
        IsCompact A ∧ Disjoint A γ.carrier := by
  intro hγ r₀ r₁ h0 h1
  subst hγ
  intro A
  refine ⟨?_, ?_⟩
  · have hK : IsCompact (OrdinaryDrawingImageWithoutEdge G D e) := by
      unfold OrdinaryDrawingImageWithoutEdge
      exact (Set.finite_range _).isCompact.union
        (isCompact_iUnion fun f => (D.edgeArc f.1).isCompact_carrier_3f48)
    exact hK.diff (Metric.isOpen_ball.union Metric.isOpen_ball)
  · rw [Set.disjoint_left]
    rintro p ⟨hpI, hpB⟩ hpc
    have hps : p ≠ (D.edgeArc e).source := fun h =>
      hpB (Or.inl (by rw [h]; exact Metric.mem_ball_self h0))
    have hpt : p ≠ (D.edgeArc e).target := fun h =>
      hpB (Or.inr (by rw [h]; exact Metric.mem_ball_self h1))
    have hri : p ∈ (D.edgeArc e).relativeInterior := by
      rw [(D.edgeArc e).relativeInterior_eq]
      refine ⟨hpc, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hps, hpt⟩
    simp only [OrdinaryDrawingImageWithoutEdge, Set.mem_union, Set.mem_range,
      Set.mem_iUnion] at hpI
    rcases hpI with ⟨v, rfl⟩ | ⟨⟨f, hf⟩, hpf⟩
    · exact D.no_vertex_in_edge_interior v e hri
    · by_cases hfi : p ∈ (D.edgeArc f).relativeInterior
      · have hmem : p ∈ D.crossingSet := (D.crossingSet_spec p).2 ⟨f, e, hf, hfi, hri⟩
        rw [Finset.card_eq_zero] at hD
        rw [hD] at hmem
        simp at hmem
      · rw [(D.edgeArc f).relativeInterior_eq] at hfi
        have hst : p = (D.edgeArc f).source ∨ p = (D.edgeArc f).target := by
          by_contra h
          exact hfi ⟨hpf, by simpa using h⟩
        obtain ⟨u, v, -, -, hc⟩ := D.edgeArc_endpoints f
        obtain ⟨w, hw⟩ : ∃ w, p = D.vertexPlacement w := by
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hst with h | h
          · exact ⟨u, h.trans h1⟩
          · exact ⟨v, h.trans h2⟩
          · exact ⟨v, h.trans h1⟩
          · exact ⟨u, h.trans h2⟩
        subst hw
        exact D.no_vertex_in_edge_interior w e hri
