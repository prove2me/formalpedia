-- Prove2me | solution 1 for PlanarQueue.Planar.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T19:38:23.566396+00:00
-- url     : https://prove2.me/submissions/fccbf2d3-2ec1-4600-8ea7-c52600c1e922

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting
import Theorems.Thm_PlanarQueue_Planar_theorem_15
import Theorems.Thm_PlanarQueue_Planar_lemma_5
import Theorems.Thm_PlanarQueue_Planar_lemma_8

set_option autoImplicit false

namespace PlanarQueueGlue

open PlanarQueue.Planar

/-- Along an edge the distance from a fixed root grows by at most one. -/
lemma dist_le_dist_add_one {V : Type} (G : SimpleGraph V) {r v w : V}
    (hr : G.Reachable r v) (h : G.Adj v w) : G.dist r w ≤ G.dist r v + 1 := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have := SimpleGraph.dist_le (p.concat h)
  rw [SimpleGraph.Walk.length_concat, hp] at this
  exact this

/-- A BFS layering is a layering. -/
lemma isLayering_of_isBFSLayering {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → ℕ) (hL : IsBFSLayering G L) : IsLayering G L := by
  obtain ⟨R, hR1, hR2⟩ := hL
  intro v w h
  obtain ⟨r, ⟨hrR, hrv⟩, -⟩ := hR1 v
  have hrw : G.Reachable r w := hrv.trans h.reachable
  rw [hR2 r hrR v hrv, hR2 r hrR w hrw]
  exact ⟨dist_le_dist_add_one G hrw h.symm, dist_le_dist_add_one G hrv h⟩

/-- Every finite graph has a BFS layering (one root per component). -/
lemma exists_isBFSLayering {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ∃ L : V → ℕ, IsBFSLayering G L := by
  classical
  let rep : V → V := fun v => Quot.out (G.connectedComponentMk v : Quot G.Reachable)
  have hrep : ∀ v, G.Reachable (rep v) v := fun v => by
    have h : G.connectedComponentMk (rep v) = G.connectedComponentMk v :=
      Quot.out_eq (G.connectedComponentMk v : Quot G.Reachable)
    exact SimpleGraph.ConnectedComponent.eq.1 h
  have hrep_eq : ∀ u v, G.Reachable u v → rep u = rep v := fun u v h => by
    have : G.connectedComponentMk u = G.connectedComponentMk v :=
      SimpleGraph.ConnectedComponent.eq.2 h
    simp only [rep, this]
  refine ⟨fun v => G.dist (rep v) v, Finset.univ.image rep, ?_, ?_⟩
  · intro v
    refine ⟨rep v, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ v), hrep v⟩, ?_⟩
    rintro r ⟨hr, hrv⟩
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hr
    rw [← hrep_eq _ _ (hrep u), hrep_eq _ _ hrv]
  · intro r hr v hrv
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hr
    show G.dist (rep v) v = G.dist (rep u) v
    rw [← hrep_eq _ _ (hrep u), hrep_eq _ _ hrv]

end PlanarQueueGlue

open PlanarQueue.Planar in
theorem solution (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPlanar G) :
    HasQueueLayout G 49 := by
  classical
  obtain ⟨L, hL⟩ := PlanarQueueGlue.exists_isBFSLayering G
  obtain ⟨P, hw, hplanar, htw⟩ := PlanarQueue.Planar.theorem_15 G hG L hL
  have hq : HasQueueLayout (quotientGraph G P) 5 :=
    PlanarQueue.Planar.lemma_5 (quotientGraph G P) hplanar htw
  let φ : V → P.parts := fun v => ⟨P.part v, P.part_mem.2 (Finset.mem_univ v)⟩
  have hmem : ∀ v : V, v ∈ (φ v).1 := fun v => P.mem_part_self.2 (Finset.mem_univ v)
  have hpart : IsHPartition G (quotientGraph G P) φ := by
    intro v w h
    by_cases hvw : φ v = φ w
    · exact Or.inl hvw
    · refine Or.inr ?_
      rw [quotientGraph, SimpleGraph.fromRel_adj]
      exact ⟨hvw, Or.inl ⟨v, hmem v, w, hmem w, h⟩⟩
  have hw' : ∀ x : P.parts, ∀ i : ℕ,
      (Finset.univ.filter fun v : V => φ v = x ∧ L v = i).card ≤ 3 := by
    intro x i
    refine le_trans (Finset.card_le_card ?_) (hw x.1 x.2 i)
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨hvx, hvi⟩ := hv
    refine ⟨?_, hvi⟩
    rw [← hvx]
    exact hmem v
  obtain ⟨ord, hord, -⟩ := PlanarQueue.Planar.lemma_8 G (quotientGraph G P) 5 3 hq L
    (PlanarQueueGlue.isLayering_of_isBFSLayering G L hL) φ hpart hw'
  have h49 : 3 * 3 * 5 + 3 * 3 / 2 = 49 := by norm_num
  rw [h49] at hord
  exact ⟨ord, hord⟩
