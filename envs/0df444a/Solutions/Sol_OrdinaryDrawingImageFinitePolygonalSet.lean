-- Prove2me | solution 1 for OrdinaryDrawingImageFinitePolygonalSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:26:40.869984+00:00
-- url     : https://prove2.me/submissions/caac45d1-b86a-470f-a438-2ac8046a0048

import Mathlib
import Definitions.Def_FinitePolygonalSet
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneFaceData

set_option autoImplicit false

open Classical

noncomputable section

namespace ODIFPS

def segSet {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
  {s | ∃ e : G.edgeFinset, ∃ i : ℕ, ∃ hi : i + 1 < (D.edgeArc e).vertices.length,
      s = ((D.edgeArc e).vertices[i], (D.edgeArc e).vertices[i + 1])}

lemma segSet_finite {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) : (segSet G D).Finite := by
  apply Set.Finite.subset (Set.finite_iUnion (fun e : G.edgeFinset =>
    (List.finite_toSet (D.edgeArc e).vertices).prod (List.finite_toSet (D.edgeArc e).vertices)))
  rintro s ⟨e, i, hi, rfl⟩
  exact Set.mem_iUnion.2 ⟨e, ⟨List.getElem_mem _, List.getElem_mem _⟩⟩

lemma inter_subsingleton {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    {s t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hs : s ∈ segSet G D) (ht : t ∈ segSet G D) (hst : s ≠ t) :
    (segment ℝ s.1 s.2 ∩ segment ℝ t.1 t.2).Subsingleton := by
  obtain ⟨e1, i, hi, rfl⟩ := hs
  obtain ⟨e2, j, hj, rfl⟩ := ht
  by_cases he : e1 = e2
  · subst he
    have hij : i ≠ j := by rintro rfl; exact hst rfl
    rcases lt_or_gt_of_ne hij with h | h
    · have := (D.edgeArc e1).segment_intersections hi hj h
      simp only
      rw [this]; split_ifs <;> simp
    · have := (D.edgeArc e1).segment_intersections hj hi h
      simp only
      rw [Set.inter_comm, this]; split_ifs <;> simp
  · intro p hp q hq
    by_contra hpq
    apply D.no_shared_nondegenerate_subarc he
    exact ⟨i, j, hi, hj, p, q, hpq,
      ((convex_segment _ _).inter (convex_segment _ _)).segment_subset hp hq⟩

lemma seg_sub {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    {s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)} (hs : s ∈ segSet G D)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ segment ℝ s.1 s.2) :
    p ∈ OrdinaryDrawingImage G D := by
  obtain ⟨e, i, hi, rfl⟩ := hs
  refine Or.inr (Set.mem_iUnion.2 ⟨e, ?_⟩)
  rw [(D.edgeArc e).carrier_eq]
  exact ⟨i, hi, hp⟩

end ODIFPS

theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) :
    ∃ K : FinitePolygonalSet, K.carrier = OrdinaryDrawingImage G D := by
  have hSf : (ODIFPS.segSet G D).Finite := ODIFPS.segSet_finite G D
  let I : Set (EuclideanSpace ℝ (Fin 2)) := ⋃ s ∈ ODIFPS.segSet G D, ⋃ t ∈ ODIFPS.segSet G D,
    {p | s ≠ t ∧ p ∈ segment ℝ s.1 s.2 ∧ p ∈ segment ℝ t.1 t.2}
  have hIf : I.Finite := hSf.biUnion fun s hs => hSf.biUnion fun t ht => by
    by_cases hst : s = t
    · simp [hst]
    · exact (ODIFPS.inter_subsingleton G D hs ht hst).finite.subset (fun p hp => ⟨hp.2.1, hp.2.2⟩)
  let P : Set (EuclideanSpace ℝ (Fin 2)) :=
    Set.range D.vertexPlacement ∪ Prod.fst '' ODIFPS.segSet G D ∪ Prod.snd '' ODIFPS.segSet G D ∪ I
  have hPf : P.Finite :=
    (((Set.finite_range _).union (hSf.image _)).union (hSf.image _)).union hIf
  refine ⟨FinitePolygonalSet.mk (OrdinaryDrawingImage G D) hPf.toFinset hSf.toFinset
    ?_ ?_ ?_ ?_, rfl⟩
  · intro s hs
    rw [Set.Finite.mem_toFinset] at hs
    obtain ⟨e, i, hi, rfl⟩ := hs
    intro h
    have := (List.Nodup.getElem_inj_iff (D.edgeArc e).simple_vertices).1 h
    omega
  · intro s hs
    rw [Set.Finite.mem_toFinset] at hs
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact ⟨Or.inl (Or.inl (Or.inr ⟨s, hs, rfl⟩)), Or.inl (Or.inr ⟨s, hs, rfl⟩)⟩
  · intro s t hs ht hst p hp hq
    rw [Set.Finite.mem_toFinset] at hs ht
    rw [Set.Finite.mem_toFinset]
    refine Or.inr ?_
    simp only [I, Set.mem_iUnion]
    exact ⟨s, hs, t, ht, hst, hp, hq⟩
  · ext p
    constructor
    · rintro (⟨v, rfl⟩ | hp)
      · exact Or.inl (by
          rw [Finset.mem_coe, Set.Finite.mem_toFinset]
          exact Or.inl (Or.inl (Or.inl ⟨v, rfl⟩)))
      · obtain ⟨e, hp⟩ := Set.mem_iUnion.1 hp
        rw [(D.edgeArc e).carrier_eq] at hp
        obtain ⟨i, hi, hp⟩ := hp
        refine Or.inr (Set.mem_iUnion.2 ⟨⟨_, (Set.Finite.mem_toFinset hSf).2 ⟨e, i, hi, rfl⟩⟩, hp⟩)
    · rintro (hp | hp)
      · rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hp
        rcases hp with ((⟨v, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩) | hp
        · exact Or.inl ⟨v, rfl⟩
        · exact ODIFPS.seg_sub G D hs (left_mem_segment _ _ _)
        · exact ODIFPS.seg_sub G D hs (right_mem_segment _ _ _)
        · simp only [I, Set.mem_iUnion] at hp
          obtain ⟨s, hs, t, ht, -, hp, -⟩ := hp
          exact ODIFPS.seg_sub G D hs hp
      · obtain ⟨⟨s, hs⟩, hp⟩ := Set.mem_iUnion.1 hp
        rw [Set.Finite.mem_toFinset] at hs
        exact ODIFPS.seg_sub G D hs hp
