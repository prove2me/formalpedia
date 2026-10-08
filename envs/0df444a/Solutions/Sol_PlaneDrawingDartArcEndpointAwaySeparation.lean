-- Prove2me | solution 1 for PlaneDrawingDartArcEndpointAwaySeparation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:47:51.190035+00:00
-- url     : https://prove2.me/submissions/5284d9ae-96a9-4598-98df-59ab7942ec06

import Mathlib
import Definitions.Def_OrdinaryDrawingImageWithoutEdge
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData

set_option autoImplicit false

open Classical in
theorem PolygonalArc.isCompact_carrier_7010 (γ : PolygonalArc) : IsCompact γ.carrier := by
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
theorem sep7010_disj {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (e : G.edgeFinset) (p : EuclideanSpace ℝ (Fin 2))
    (hpI : p ∈ OrdinaryDrawingImageWithoutEdge G D e)
    (hpc : p ∈ (D.edgeArc e).carrier)
    (hps : p ≠ (D.edgeArc e).source) (hpt : p ≠ (D.edgeArc e).target) : False := by
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

open Classical in
theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) (d : G.Dart) (r₀ r₁ : ℝ) :
    0 < r₀ →
      0 < r₁ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x : EuclideanSpace ℝ (Fin 2),
            x ∈ OrdinaryDrawingImageWithoutEdge G D (A.dartEdge d) →
              x ∉ Metric.ball (A.dartArc d).source r₀ ∪
                Metric.ball (A.dartArc d).target r₁ →
                ∀ p : EuclideanSpace ℝ (Fin 2),
                  p ∈ (A.dartArc d).carrier →
                    δ ≤ dist x p := by
  intro h0 h1
  set e := A.dartEdge d with he
  set S : Set (EuclideanSpace ℝ (Fin 2)) := OrdinaryDrawingImageWithoutEdge G D e \
    (Metric.ball (A.dartArc d).source r₀ ∪ Metric.ball (A.dartArc d).target r₁) with hS
  have hWc : IsCompact (OrdinaryDrawingImageWithoutEdge G D e) := by
    unfold OrdinaryDrawingImageWithoutEdge
    exact (Set.finite_range _).isCompact.union
      (isCompact_iUnion fun f => (D.edgeArc f.1).isCompact_carrier_7010)
  have hSc : IsClosed S := (hWc.diff (Metric.isOpen_ball.union Metric.isOpen_ball)).isClosed
  have hK : IsCompact (A.dartArc d).carrier := (A.dartArc d).isCompact_carrier_7010
  -- endpoints of the dart arc are the endpoints of the edge arc
  have hends : ∀ q : EuclideanSpace ℝ (Fin 2),
      q ≠ (A.dartArc d).source → q ≠ (A.dartArc d).target →
        q ≠ (D.edgeArc e).source ∧ q ≠ (D.edgeArc e).target := by
    intro q hs ht
    rcases A.dartArc_orientation d with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h] at hs ht; exact ⟨hs, ht⟩
    · rw [h] at hs ht
      exact ⟨ht, hs⟩
  have hdisj : Disjoint (A.dartArc d).carrier S := by
    rw [Set.disjoint_left]
    rintro p hpc ⟨hpI, hpB⟩
    have hps : p ≠ (A.dartArc d).source := fun h =>
      hpB (Or.inl (by rw [h]; exact Metric.mem_ball_self h0))
    have hpt : p ≠ (A.dartArc d).target := fun h =>
      hpB (Or.inr (by rw [h]; exact Metric.mem_ball_self h1))
    obtain ⟨h1', h2'⟩ := hends p hps hpt
    rw [A.dartArc_carrier d] at hpc
    exact sep7010_disj G D hD e p hpI hpc h1' h2'
  obtain ⟨r, hr0, hr⟩ := Metric.exists_pos_forall_lt_edist hK hSc hdisj
  refine ⟨r, by exact_mod_cast hr0, ?_⟩
  intro x hx hxB p hp
  have := hr p hp x ⟨hx, hxB⟩
  rw [edist_nndist, ENNReal.coe_lt_coe] at this
  rw [dist_comm, dist_nndist]
  exact_mod_cast this.le
