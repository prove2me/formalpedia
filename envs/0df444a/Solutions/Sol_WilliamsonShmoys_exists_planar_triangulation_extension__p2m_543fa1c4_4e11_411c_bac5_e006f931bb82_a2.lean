-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension__p2m_543fa1c4_4e11_411c_bac5_e006f931bb82_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:32.607236+00:00
-- url     : https://prove2.me/submissions/8f0305ec-526d-403f-adc8-0b07dab9badf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_419df074_7ffa_4f7d_9922_608f3a25f504_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_419df074_7ffa_4f7d_9922_608f3a25f504_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H' : SimpleGraph V,
      H ≤ H' ∧ WilliamsonShmoys.HasPlanarDrawingOn H' ∧
        3 * Fintype.card V - 6 = H'.edgeSet.ncard := by
  obtain ⟨H', hHH', hDraw', hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_419df074_7ffa_4f7d_9922_608f3a25f504_a1
      H hDraw
  exact ⟨H', hHH', hDraw',
    WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_419df074_7ffa_4f7d_9922_608f3a25f504_a1
      H' hDraw' hV hmax⟩