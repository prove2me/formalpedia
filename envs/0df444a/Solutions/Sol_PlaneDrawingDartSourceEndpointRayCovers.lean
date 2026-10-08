-- Prove2me | solution 1 for PlaneDrawingDartSourceEndpointRayCovers
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:17:27.87999+00:00
-- url     : https://prove2.me/submissions/17d4f5c8-921b-4d2a-b022-2eba6fea5fc4

import Mathlib
import Definitions.Def_PolygonalArc
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData

open Classical

set_option autoImplicit false

theorem e917_segment_isClosed (x y : EuclideanSpace ℝ (Fin 2)) :
    IsClosed (segment ℝ x y) := by
  rw [segment_eq_image]
  exact (isCompact_Icc.image (by fun_prop)).isClosed

theorem e917_src_eq (γ : PolygonalArc) (h0 : 0 < γ.vertices.length) :
    γ.vertices[0] = γ.source := by
  have h := γ.source_eq_head
  rw [List.head?_eq_getElem?] at h
  rw [List.getElem?_eq_getElem h0] at h
  exact Option.some.inj h

theorem e917_src_not_mem (γ : PolygonalArc) (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (h1 : 1 ≤ j) : γ.source ∉ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
  have h0 : 0 < γ.vertices.length := by omega
  rw [← e917_src_eq γ h0]
  intro hm
  have hnd := γ.simple_vertices
  have hne1 : γ.vertices[0] ≠ γ.vertices[j] := by
    intro h
    have := (List.Nodup.getElem_inj_iff hnd).1 h
    omega
  have hne2 : γ.vertices[0] ≠ γ.vertices[j + 1] := by
    intro h
    have := (List.Nodup.getElem_inj_iff hnd).1 h
    omega
  have hav := γ.vertices_avoid_nonincident_interiors (i := j) (k := 0) hj h0 (by omega) (by omega)
  rw [← insert_endpoints_openSegment] at hm
  rcases hm with h | h | h
  · exact hne1 h
  · exact hne2 h
  · exact hav h

theorem e917_arc_ray (γ : PolygonalArc) :
    ∃ r : ℝ, 0 < r ∧
      (∀ hfirst : 1 < γ.vertices.length,
       Metric.ball γ.source r ∩ γ.carrier ⊆
        {x | ∃ c : ℝ, 0 ≤ c ∧
          x = γ.source + c • (γ.vertices[1]'hfirst - γ.source)}) := by
  classical
  set n := γ.vertices.length with hn
  let f : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun j =>
    if h : j + 1 < γ.vertices.length then
      (if 1 ≤ j then segment ℝ γ.vertices[j] γ.vertices[j + 1] else ∅) else ∅
  let S := ⋃ j ∈ Finset.range n, f j
  have hS : IsClosed S := by
    refine isClosed_biUnion_finset (fun j _ => ?_)
    simp only [f]
    split_ifs
    · exact e917_segment_isClosed _ _
    · exact isClosed_empty
    · exact isClosed_empty
  have hnot : γ.source ∉ S := by
    simp only [S, f, Set.mem_iUnion]
    rintro ⟨j, _, hj⟩
    split_ifs at hj with h1 h2
    · exact e917_src_not_mem γ j h1 h2 hj
    · exact hj
    · exact hj
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl γ.source hnot
  refine ⟨r, hr, ?_⟩
  intro hfirst x hxx
  obtain ⟨hxb, hxc⟩ := hxx
  rw [γ.carrier_eq] at hxc
  obtain ⟨i, hi, hx⟩ := hxc
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · have h0 : 0 < γ.vertices.length := by omega
    have hs := e917_src_eq γ h0
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
    refine ⟨b, hb, ?_⟩
    simp only [zero_add] at *
    rw [hs]
    have : a = 1 - b := by linarith
    subst this
    rw [smul_sub, sub_smul, one_smul]
    abel
  · exfalso
    have hxS : x ∈ S := by
      simp only [S, f, Set.mem_iUnion]
      refine ⟨i, Finset.mem_range.2 (by omega), ?_⟩
      rw [dif_pos hi, if_pos (show 1 ≤ i by omega)]
      exact hx
    exact hball hxb hxS

theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D) :
    ∃ sourceRayRadius :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} → ℝ,
      (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        0 < sourceRayRadius v d) ∧
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        let γ := A.dartArc d.1
        let hfirst : 1 < γ.vertices.length :=
          Nat.lt_of_succ_le γ.length_ge_two
        Metric.ball (D.vertexPlacement v) (sourceRayRadius v d) ∩
            (D.edgeArc (A.dartEdge d.1)).carrier ⊆
          {x | ∃ c : ℝ, 0 ≤ c ∧
            x = D.vertexPlacement v +
              c • (γ.vertices[1]'hfirst - D.vertexPlacement v)} := by
  refine ⟨fun v d => Classical.choose (e917_arc_ray (A.dartArc d.1)),
    fun v d => (Classical.choose_spec (e917_arc_ray (A.dartArc d.1))).1, ?_⟩
  intro v d γ hfirst x hx
  have hspec := (Classical.choose_spec (e917_arc_ray (A.dartArc d.1))).2 hfirst
  have hsrc : (A.dartArc d.1).source = D.vertexPlacement v := by
    rw [A.dartArc_source d.1, d.2]
  rw [← A.dartArc_carrier d.1, ← hsrc] at hx
  have := hspec hx
  simpa [γ, hsrc] using this
