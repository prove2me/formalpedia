-- Prove2me | solution 1 for PlaneDrawingDartVertexLocalDiskIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:47:47.240979+00:00
-- url     : https://prove2.me/submissions/abdddb86-43db-49d9-9023-66eb9eee31f6

import Mathlib
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneFaceData

set_option autoImplicit false

open Classical

theorem g399_segment_isClosed (x y : EuclideanSpace ℝ (Fin 2)) :
    IsClosed (segment ℝ x y) := by
  rw [segment_eq_image]
  exact (isCompact_Icc.image (by fun_prop)).isClosed

theorem g399_carrier_isClosed (γ : PolygonalArc) : IsClosed γ.carrier := by
  rw [γ.carrier_eq]
  have hs : {p | ∃ i : ℕ, ∃ hi : i + 1 < γ.vertices.length,
      p ∈ segment ℝ γ.vertices[i] γ.vertices[i + 1]} =
      ⋃ i ∈ Finset.range γ.vertices.length, ⋃ (hi : i + 1 < γ.vertices.length),
        segment ℝ γ.vertices[i] γ.vertices[i + 1] := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, hp⟩; exact ⟨i, by omega, hi, hp⟩
    · rintro ⟨i, _, hi, hp⟩; exact ⟨i, hi, hp⟩
  rw [hs]
  refine isClosed_biUnion_finset (fun i _ => isClosed_iUnion_of_finite fun hi => ?_)
  exact g399_segment_isClosed _ _

theorem g399_src_eq (γ : PolygonalArc) (h0 : 0 < γ.vertices.length) :
    γ.vertices[0] = γ.source := by
  have h := γ.source_eq_head
  rw [List.head?_eq_getElem?] at h
  rw [List.getElem?_eq_getElem h0] at h
  exact Option.some.inj h

theorem g399_src_not_mem (γ : PolygonalArc) (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (h1 : 1 ≤ j) : γ.source ∉ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
  have h0 : 0 < γ.vertices.length := by omega
  rw [← g399_src_eq γ h0]
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

theorem g399_ev_tail (γ : PolygonalArc) :
    ∀ᶠ x in nhds γ.source, ∀ i (hi : i + 1 < γ.vertices.length), 1 ≤ i →
      x ∉ segment ℝ γ.vertices[i] γ.vertices[i + 1] := by
  let f : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun j =>
    if h : j + 1 < γ.vertices.length then
      (if 1 ≤ j then segment ℝ γ.vertices[j] γ.vertices[j + 1] else ∅) else ∅
  let S := ⋃ j ∈ Finset.range γ.vertices.length, f j
  have hS : IsClosed S := by
    refine isClosed_biUnion_finset (fun j _ => ?_)
    simp only [f]
    split_ifs
    · exact g399_segment_isClosed _ _
    · exact isClosed_empty
    · exact isClosed_empty
  have hnot : γ.source ∉ S := by
    simp only [S, f, Set.mem_iUnion]
    rintro ⟨j, _, hj⟩
    split_ifs at hj with h1 h2
    · exact g399_src_not_mem γ j h1 h2 hj
    · exact hj
    · exact hj
  filter_upwards [hS.isOpen_compl.mem_nhds hnot] with x hx i hi h1 hxs
  apply hx
  simp only [S, f, Set.mem_iUnion]
  refine ⟨i, Finset.mem_range.2 (by omega), ?_⟩
  rw [dif_pos hi, if_pos h1]
  exact hxs

theorem g399_v1_ne (γ : PolygonalArc) :
    γ.vertices[1]'(Nat.lt_of_succ_le γ.length_ge_two) ≠ γ.source := by
  have h0 : 0 < γ.vertices.length := by have := γ.length_ge_two; omega
  rw [← g399_src_eq γ h0]
  intro h
  have := (List.Nodup.getElem_inj_iff γ.simple_vertices).1 h
  omega

theorem g399_sub (p0 p1 : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : 0 < ρ)
    (hρL : ρ ≤ ‖p1 - p0‖) :
    openSegment ℝ p0 (p0 + ρ • (‖p1 - p0‖⁻¹ • (p1 - p0))) ⊆ segment ℝ p0 p1 := by
  have hL : 0 < ‖p1 - p0‖ := lt_of_lt_of_le hρ hρL
  have hq : p0 + ρ • (‖p1 - p0‖⁻¹ • (p1 - p0)) ∈ segment ℝ p0 p1 := by
    rw [segment_eq_image']
    refine ⟨ρ * ‖p1 - p0‖⁻¹, ⟨by positivity, ?_⟩, ?_⟩
    · rw [← div_eq_mul_inv, div_le_one hL]; exact hρL
    · simp only [smul_smul]
  exact (openSegment_subset_segment _ _ _).trans
    ((convex_segment p0 p1).segment_subset (left_mem_segment _ _ _) hq)

theorem g399_mem (p0 p1 x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : 0 < ρ)
    (hρL : ρ ≤ ‖p1 - p0‖)
    (hx : x ∈ segment ℝ p0 p1) (hd : dist x p0 < ρ) (hx0 : x ≠ p0) :
    x ∈ openSegment ℝ p0 (p0 + ρ • (‖p1 - p0‖⁻¹ • (p1 - p0))) := by
  have hL : 0 < ‖p1 - p0‖ := lt_of_lt_of_le hρ hρL
  rw [segment_eq_image'] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  have hdist : dist (p0 + t • (p1 - p0)) p0 = t * ‖p1 - p0‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht0 with h | h
    · exact h
    · subst h; simp at hx0
  rw [openSegment_eq_image']
  refine ⟨t * ‖p1 - p0‖ / ρ, ⟨div_pos (mul_pos htpos hL) hρ, ?_⟩, ?_⟩
  · rw [div_lt_one hρ]; rw [hdist] at hd; exact hd
  · simp only [add_sub_cancel_left, smul_smul]
    congr 2
    field_simp

theorem g399_dist (p0 p1 x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : 0 < ρ)
    (hne : p1 ≠ p0)
    (hx : x ∈ openSegment ℝ p0 (p0 + ρ • (‖p1 - p0‖⁻¹ • (p1 - p0)))) :
    dist x p0 < ρ := by
  have hL : 0 < ‖p1 - p0‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  rw [openSegment_eq_image'] at hx
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
  rw [dist_eq_norm, add_sub_cancel_left, add_sub_cancel_left, norm_smul, norm_smul, norm_smul,
    norm_inv, norm_norm, Real.norm_of_nonneg h0.le, Real.norm_of_nonneg hρ.le,
    inv_mul_cancel₀ hL.ne', mul_one]
  nlinarith

theorem g399_notmem {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (v : V) (e : G.edgeFinset) (hv : v ∉ e.1) :
    D.vertexPlacement v ∉ (D.edgeArc e).carrier := by
  intro hc
  have hri := D.no_vertex_in_edge_interior v e
  rw [(D.edgeArc e).relativeInterior_eq] at hri
  have hst : D.vertexPlacement v = (D.edgeArc e).source ∨
      D.vertexPlacement v = (D.edgeArc e).target := by
    by_contra h
    push_neg at h
    exact hri ⟨hc, by simp [h.1, h.2]⟩
  obtain ⟨u, w, _, he, hends⟩ := D.edgeArc_endpoints e
  have key : D.vertexPlacement v = D.vertexPlacement u ∨
      D.vertexPlacement v = D.vertexPlacement w := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hst with h | h
    · exact Or.inl (h.trans h1)
    · exact Or.inr (h.trans h2)
    · exact Or.inr (h.trans h1)
    · exact Or.inl (h.trans h2)
  apply hv
  rw [he]
  rcases key with h | h
  · rw [D.vertexPlacement_injective h]; exact Sym2.mem_mk_left _ _
  · rw [D.vertexPlacement_injective h]; exact Sym2.mem_mk_right _ _

def g399Good {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D) (v : V)
    (x : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (∀ w : V, w ≠ v → x ≠ D.vertexPlacement w) ∧
  (∀ e : G.edgeFinset, v ∉ e.1 → x ∉ (D.edgeArc e).carrier) ∧
  (∀ d : {d : G.Dart // d.toProd.1 = v}, ∀ i (hi : i + 1 < (A.dartArc d.1).vertices.length),
      1 ≤ i → x ∉ segment ℝ (A.dartArc d.1).vertices[i] (A.dartArc d.1).vertices[i + 1]) ∧
  (∀ d : {d : G.Dart // d.toProd.1 = v},
      x ≠ (A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two))

theorem g399_ev {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D) (v : V) :
    ∀ᶠ x in nhds (D.vertexPlacement v), g399Good G D A v x := by
  have hsrc : ∀ d : {d : G.Dart // d.toProd.1 = v},
      (A.dartArc d.1).source = D.vertexPlacement v := fun d => by
    rw [A.dartArc_source, d.2]
  unfold g399Good
  refine (Filter.eventually_all.2 ?_).and ((Filter.eventually_all.2 ?_).and
    ((Filter.eventually_all.2 ?_).and (Filter.eventually_all.2 ?_)))
  · intro w
    by_cases hw : w = v
    · exact Filter.Eventually.of_forall (fun x h => absurd hw h)
    · filter_upwards [eventually_ne_nhds (fun h => hw (D.vertexPlacement_injective h).symm)]
        with x hx _ using hx
  · intro e
    by_cases he : v ∈ e.1
    · exact Filter.Eventually.of_forall (fun x h => absurd he h)
    · filter_upwards [(g399_carrier_isClosed _).isOpen_compl.mem_nhds (g399_notmem G D v e he)]
        with x hx _ using hx
  · intro d
    rw [← hsrc d]
    exact g399_ev_tail _
  · intro d
    rw [← hsrc d]
    exact eventually_ne_nhds (g399_v1_ne _).symm

theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    ∃ localDiskRadius : V → ℝ,
      ∃ germDirection :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2),
      ∃ radialGerm :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
          Set (EuclideanSpace ℝ (Fin 2)),
        (∀ v : V, 0 < localDiskRadius v) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d ≠ 0) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d =
            (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖)⁻¹ •
              ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d =
            openSegment ℝ (D.vertexPlacement v)
              (D.vertexPlacement v + localDiskRadius v • germDirection v d)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d ⊆ (D.edgeArc (A.dartEdge d.1)).carrier) ∧
        (∀ v : V,
          Metric.ball (D.vertexPlacement v) (localDiskRadius v) ∩
              OrdinaryDrawingImage G D =
            {D.vertexPlacement v} ∪
              ⋃ d : {d : G.Dart // d.toProd.1 = v}, radialGerm v d) := by
  have key : ∀ v : V, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ Metric.ball (D.vertexPlacement v) ρ, g399Good G D A v x :=
    fun v => Metric.eventually_nhds_iff_ball.1 (g399_ev G D A v)
  choose ρ hρ hgood using key
  have hsrc : ∀ d : G.Dart,
      (A.dartArc d).vertices[0]'(by have := (A.dartArc d).length_ge_two; omega) =
        D.vertexPlacement d.toProd.1 := fun d => by
    rw [g399_src_eq, A.dartArc_source]
  have hne : ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      (A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) ≠
        D.vertexPlacement v := fun v d => by
    have := g399_v1_ne (A.dartArc d.1)
    rwa [A.dartArc_source, d.2] at this
  have hρL : ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      ρ v ≤ ‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
        D.vertexPlacement v‖ := by
    intro v d
    by_contra h
    push_neg at h
    exact (hgood v _ (by rw [Metric.mem_ball, dist_eq_norm]; exact h)).2.2.2 d rfl
  have hsub : ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
      openSegment ℝ (D.vertexPlacement v) (D.vertexPlacement v + ρ v •
        (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
          D.vertexPlacement v‖⁻¹ •
        ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
          D.vertexPlacement v))) ⊆ (D.edgeArc (A.dartEdge d.1)).carrier := by
    intro v d x hx
    rw [← A.dartArc_carrier, (A.dartArc d.1).carrier_eq]
    refine ⟨0, Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two, ?_⟩
    have h := g399_sub _ _ (ρ v) (hρ v) (hρL v d) hx
    have h0 := hsrc d.1
    rw [d.2] at h0
    rw [h0]
    exact h
  refine ⟨ρ, fun v d =>
      ‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
          D.vertexPlacement v‖⁻¹ •
        ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
          D.vertexPlacement v),
    fun v d => openSegment ℝ (D.vertexPlacement v) (D.vertexPlacement v + ρ v •
        (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
          D.vertexPlacement v‖⁻¹ •
        ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
          D.vertexPlacement v))),
    hρ, ?_, fun _ _ => rfl, fun _ _ => rfl, hsub, ?_⟩
  · intro v d
    have h := sub_ne_zero.2 (hne v d)
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 h)) h
  · intro v
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨hxb, hxI⟩
      have hg := hgood v x hxb
      by_cases hx0 : x = D.vertexPlacement v
      · exact Or.inl hx0
      right
      unfold OrdinaryDrawingImage at hxI
      rcases hxI with ⟨w, rfl⟩ | hxI
      · exfalso
        by_cases hw : w = v
        · exact hx0 (hw ▸ rfl)
        · exact hg.1 w hw rfl
      · rw [Set.mem_iUnion] at hxI
        obtain ⟨e, hxe⟩ := hxI
        by_cases hve : v ∈ e.1
        swap
        · exact absurd hxe (hg.2.1 e hve)
        obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 hve
        have hadj : G.Adj v w := by
          have := e.2
          rw [SimpleGraph.mem_edgeFinset, hw, SimpleGraph.mem_edgeSet] at this
          exact this
        let d : G.Dart := ⟨(v, w), hadj⟩
        have hde : A.dartEdge d = e := Subtype.ext ((A.dartEdge_eq d).trans hw.symm)
        refine ⟨⟨d, rfl⟩, ?_⟩
        rw [← hde, ← A.dartArc_carrier, (A.dartArc d).carrier_eq] at hxe
        obtain ⟨i, hi, hxs⟩ := hxe
        have hi0 : i = 0 := by
          by_contra h
          exact hg.2.2.1 ⟨d, rfl⟩ i hi (by omega) hxs
        subst hi0
        have h0 := hsrc d
        rw [h0] at hxs
        exact g399_mem _ _ x (ρ v) (hρ v) (hρL v ⟨d, rfl⟩) hxs
          (by rwa [Metric.mem_ball] at hxb) hx0
    · rintro (rfl | ⟨d, hxd⟩)
      · exact ⟨Metric.mem_ball_self (hρ v), Or.inl ⟨v, rfl⟩⟩
      · refine ⟨?_, Or.inr (Set.mem_iUnion.2 ⟨A.dartEdge d.1, hsub v d hxd⟩)⟩
        rw [Metric.mem_ball]
        exact g399_dist _ _ x (ρ v) (hρ v) (hne v d) hxd
