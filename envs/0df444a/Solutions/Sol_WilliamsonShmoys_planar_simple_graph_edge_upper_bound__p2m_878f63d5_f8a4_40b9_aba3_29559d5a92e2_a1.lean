-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:43.058154+00:00
-- url     : https://prove2.me/submissions/026901fe-0c93-45c9-994b-334489a33dd5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, _hN, hNcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4
      M hM hV
  calc
    M.edgeSet.ncard ≤ N.edgeSet.ncard :=
      WilliamsonShmoys.edgeSet_ncard_mono__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4
        M N hMN
    _ = 3 * Fintype.card V - 6 := hNcard