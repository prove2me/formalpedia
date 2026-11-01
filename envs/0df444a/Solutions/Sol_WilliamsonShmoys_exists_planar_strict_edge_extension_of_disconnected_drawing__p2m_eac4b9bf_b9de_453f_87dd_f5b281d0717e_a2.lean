-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_strict_edge_extension_of_disconnected_drawing__p2m_eac4b9bf_b9de_453f_87dd_f5b281d0717e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:11:24.02955+00:00
-- url     : https://prove2.me/submissions/e11c89b3-7036-479a-bc89-e8a2f6f8fd6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_drawing_is_connected__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
import Theorems.Thm_WilliamsonShmoys_connected_extension_has_new_edge__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hdisconnected : ¬ K.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Adj u v ∧
      ∃ L : SimpleGraph V,
        K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.Adj u v := by
  obtain ⟨M, hKM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3 K hK
  have hMconn :=
    WilliamsonShmoys.inclusion_maximal_planar_drawing_is_connected__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3 M hM hmax
  obtain ⟨u, v, huv, hnot, hMv⟩ :=
    WilliamsonShmoys.connected_extension_has_new_edge__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3 K M hKM hdisconnected hMconn
  exact ⟨u, v, huv, hnot, M, hKM, hM, hMv⟩