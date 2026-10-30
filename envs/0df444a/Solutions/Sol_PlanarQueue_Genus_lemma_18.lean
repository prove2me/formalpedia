-- Prove2me | solution 1 for PlanarQueue.Genus.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T19:46:22.163967+00:00
-- url     : https://prove2.me/submissions/53e2f2bd-4017-4607-99de-dab2e38d2ed7

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_PlanarQueue_Genus_Setting
import Theorems.Thm_PlanarQueue_Planar_theorem_15
import Theorems.Thm_PlanarQueue_Planar_lemma_5
import Theorems.Thm_PlanarQueue_Planar_lemma_8

set_option autoImplicit false

namespace PlanarQueueGlue18

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

end PlanarQueueGlue18

theorem solution (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : RobertsonSeymour1986.GM5.IsPlanar G) (L : V → ℕ) (hL : PlanarQueue.Genus.IsBFSLayering G L) :
    ∃ ord : V → ℕ, PlanarQueue.Planar.OrderAdmits G 49 ord ∧ ∀ v w : V, L v < L w → ord v < ord w := by
  classical
  have hL' : PlanarQueue.Planar.IsBFSLayering G L := hL
  obtain ⟨P, hw, hplanar, htw⟩ := PlanarQueue.Planar.theorem_15 G hG L hL'
  have hq : PlanarQueue.Planar.HasQueueLayout (PlanarQueue.Planar.quotientGraph G P) 5 :=
    PlanarQueue.Planar.lemma_5 (PlanarQueue.Planar.quotientGraph G P) hplanar htw
  let φ : V → P.parts := fun v => ⟨P.part v, P.part_mem.2 (Finset.mem_univ v)⟩
  have hmem : ∀ v : V, v ∈ (φ v).1 := fun v => P.mem_part_self.2 (Finset.mem_univ v)
  have hpart : PlanarQueue.Planar.IsHPartition G (PlanarQueue.Planar.quotientGraph G P) φ := by
    intro v w h
    by_cases hvw : φ v = φ w
    · exact Or.inl hvw
    · refine Or.inr ?_
      rw [PlanarQueue.Planar.quotientGraph, SimpleGraph.fromRel_adj]
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
  obtain ⟨ord, hord, hmono⟩ := PlanarQueue.Planar.lemma_8 G (PlanarQueue.Planar.quotientGraph G P) 5 3 hq L
    (PlanarQueueGlue18.isLayering_of_isBFSLayering G L hL') φ hpart hw'
  have h49 : 3 * 3 * 5 + 3 * 3 / 2 = 49 := by norm_num
  rw [h49] at hord
  exact ⟨ord, hord, hmono⟩
