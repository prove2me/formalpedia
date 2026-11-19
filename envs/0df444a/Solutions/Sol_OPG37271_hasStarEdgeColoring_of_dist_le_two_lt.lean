-- Prove2me | solution 1 for OPG37271.hasStarEdgeColoring_of_dist_le_two_lt
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:48:08.802162+00:00
-- url     : https://prove2.me/submissions/3cf27e0c-88ae-463f-a6a7-5a15deb8f81c

import Definitions.Def_opg37271_star_edge_coloring
import Theorems.Thm_OPG37271_isStarEdgeColoring_insert_edge
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Card

set_option autoImplicit false

open OPG37271

universe u

theorem solution {V : Type u} {G : SimpleGraph V} {k : ℕ}
    (u v : V) (huv : G.Adj u v)
    (hc' : HasStarEdgeColoring (G.deleteEdges {s(u, v)}) k)
    (hbound : ∃ S : Finset (Sym2 V), S.card < k ∧
      ∀ x y : V, G.Adj x y → s(x, y) ≠ s(u, v) →
        (x = u ∨ x = v ∨ y = u ∨ y = v ∨ G.Adj u x ∨ G.Adj v x ∨ G.Adj u y ∨ G.Adj v y) →
        s(x, y) ∈ S) :
    HasStarEdgeColoring G k := by
  classical
  rcases hc' with ⟨c', hc'_star⟩
  rcases hbound with ⟨S, hS_card, hS_mem⟩
  let used : Finset (Fin k) :=
    S.attach.image fun e =>
      if he : e.1 ∈ (G.deleteEdges {s(u, v)}).edgeSet then c' ⟨e.1, he⟩ else ⟨0, Nat.zero_lt_of_lt hS_card⟩
  have hused_card : used.card < k := by
    calc used.card ≤ S.attach.card := Finset.card_image_le
      _ = S.card := Finset.card_attach
      _ < k := hS_card
  have hex : ∃ col : Fin k, col ∉ used := by
    by_contra hnone
    push Not at hnone
    have hle := Finset.card_le_card (s := Finset.univ) (fun x _ => hnone x)
    rw [Finset.card_fin] at hle
    omega
  rcases hex with ⟨col, hcol⟩
  let c : EdgeColoring G (Fin k) := fun e =>
    if he : e.1 = s(u, v) then col
    else c' ⟨e.1, by
      rcases e with ⟨⟨x, y⟩, hxy⟩
      exact SimpleGraph.deleteEdges_adj.mpr ⟨hxy, he⟩⟩
  refine ⟨c, OPG37271.isStarEdgeColoring_insert_edge u v huv c ?_ ?_⟩
  · have heq : (fun e => c ⟨e.1, SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le {s(u, v)}) e.2⟩ :
        EdgeColoring (G.deleteEdges {s(u, v)}) (Fin k)) = c' := by
      funext ⟨e, he⟩
      have hne : e ≠ s(u, v) := by
        rcases e with ⟨x, y⟩
        exact (SimpleGraph.deleteEdges_adj.mp he).2
      simp only [c, dif_neg hne]
    rw [heq]
    exact hc'_star
  · intro x y hxy hne hdist
    have hmem : s(x, y) ∈ S := hS_mem x y hxy hne hdist
    have hrest : s(x, y) ∈ (G.deleteEdges {s(u, v)}).edgeSet :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hxy, hne⟩
    have hc_xy : c.get x y hxy = c' ⟨s(x, y), hrest⟩ := by
      simp only [SimpleGraph.EdgeLabeling.get, c, dif_neg hne]
    have hc_uv : c.get u v huv = col := by
      simp only [SimpleGraph.EdgeLabeling.get, c, dif_pos rfl]
    rw [hc_xy, hc_uv]
    intro heq
    apply hcol
    refine Finset.mem_image.mpr ⟨⟨s(x, y), hmem⟩, Finset.mem_attach _ _, ?_⟩
    simp only [dif_pos hrest, heq]
