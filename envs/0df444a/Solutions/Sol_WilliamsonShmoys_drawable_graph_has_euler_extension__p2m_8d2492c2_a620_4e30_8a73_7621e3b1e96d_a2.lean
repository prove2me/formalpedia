-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_euler_extension__p2m_8d2492c2_a620_4e30_8a73_7621e3b1e96d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:14:27.958407+00:00
-- url     : https://prove2.me/submissions/153d93be-6550-47ed-9bfa-f2f7c147edbb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_euler_extension_exists_maximal_extension__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_euler_extension_maximal_planar_edge_count__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       L.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_euler_extension_exists_maximal_extension__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
      K hV hK
  have hcount :=
    WilliamsonShmoys.drawable_graph_has_euler_extension_maximal_planar_edge_count__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
      L hV hL hmax
  exact ⟨L, hKL, hL, hcount⟩