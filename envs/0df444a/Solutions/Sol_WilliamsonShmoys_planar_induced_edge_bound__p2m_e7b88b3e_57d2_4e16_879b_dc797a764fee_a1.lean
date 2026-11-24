-- Prove2me | solution 1 for WilliamsonShmoys.planar_induced_edge_bound__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:42:19.414553+00:00
-- url     : https://prove2.me/submissions/5f3def18-5e2f-460e-8e8c-8aa8b27b28fb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_induce

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (s : Finset V) :
    if 3 ≤ s.card then
      (L.induce (fun v => v ∈ s)).edgeSet.ncard ≤ 3 * s.card - 6
    else if 2 ≤ s.card then
      (L.induce (fun v => v ∈ s)).edgeSet.ncard ≤ 1
    else
      (L.induce (fun v => v ∈ s)).edgeSet.ncard = 0 := by
  classical
  have hd : HasPlanarDrawingOn (L.induce (↑s : Set V)) := WilliamsonShmoys.planar_drawing_induce L hL s
  have hc : Fintype.card (↑s : Set V) = s.card := by simp
  have hch : (L.induce (↑s : Set V)).edgeSet.ncard ≤ (s.card).choose 2 := by
    rw [← hc, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    exact SimpleGraph.card_edgeFinset_le_card_choose_two
  show if 3 ≤ s.card then (L.induce (↑s : Set V)).edgeSet.ncard ≤ 3 * s.card - 6
    else if 2 ≤ s.card then (L.induce (↑s : Set V)).edgeSet.ncard ≤ 1
    else (L.induce (↑s : Set V)).edgeSet.ncard = 0
  split_ifs with h3 h2
  · have := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc (L.induce (↑s : Set V)) (by omega) hd
    omega
  · have : s.card = 2 := by omega
    rw [this] at hch
    simpa using hch
  · have : (s.card).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    omega
