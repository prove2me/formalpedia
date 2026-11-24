-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_by_bridging_components__p2m_9d6795a0_df2a_4cd4_b626_1874c3a84ac3_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:36.390802+00:00
-- url     : https://prove2.me/submissions/e28d9ea2-f269-4ee5-b3d6-8aa9779d6c86

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : ¬ L.Connected)
    (hV : 2 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v, H.Adj u v ∧ ¬ L.Adj u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ L.Reachable a b := by
    by_contra hc
    push_neg at hc
    exact hconn ⟨hc⟩
  obtain ⟨H, hLH, hH⟩ := WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 L hL a b hab
  obtain ⟨u, v, h1, h2⟩ : ∃ u v, H.Adj u v ∧ ¬ L.Adj u v := by
    by_contra hc
    push_neg at hc
    exact hLH.ne (le_antisymm hLH.le (fun x y h => hc x y h))
  exact ⟨H, hLH.le, hH, u, v, h1, h2⟩
