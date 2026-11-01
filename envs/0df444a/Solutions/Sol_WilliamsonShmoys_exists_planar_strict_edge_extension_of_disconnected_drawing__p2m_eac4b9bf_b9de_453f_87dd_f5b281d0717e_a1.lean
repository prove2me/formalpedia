-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_strict_edge_extension_of_disconnected_drawing__p2m_eac4b9bf_b9de_453f_87dd_f5b281d0717e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:36:44.511839+00:00
-- url     : https://prove2.me/submissions/98473c3f-4849-4da3-8797-a885662f4651
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_connected_strict_edge_extension__p2m_d4845ee8_5b33_4e78_bf1a_df62eb784c7d_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hdisconnected : ¬ K.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Adj u v ∧
      ∃ L : SimpleGraph V,
        K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.Adj u v := by
  obtain ⟨u, v, huv, hnot, L, hKL, hLplanar, hLuv, _hLconnected⟩ :=
    WilliamsonShmoys.planar_connected_strict_edge_extension__p2m_d4845ee8_5b33_4e78_bf1a_df62eb784c7d_a2
      K hK hdisconnected
  exact ⟨u, v, huv, hnot, L, hKL, hLplanar, hLuv⟩