-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_graph_has_drawable_extension__p2m_eec88a46_e2f1_426a_bbcb_0322b031599d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:07:49.9218+00:00
-- url     : https://prove2.me/submissions/7f82b106-5b0e-4597-886d-75e282bb294e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_disconnected_has_nonreachable_pair__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_nonreachable_vertices__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) (hdisconn : ¬ N.Connected) :
    ∃ P : SimpleGraph V, N ≤ P ∧ P ≠ N ∧ HasPlanarDrawingOn P := by
  obtain ⟨u, v, hsep⟩ :=
    WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
      N hcard hdisconn
  exact WilliamsonShmoys.planar_add_edge_between_nonreachable_vertices__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
    N u v hsep hN