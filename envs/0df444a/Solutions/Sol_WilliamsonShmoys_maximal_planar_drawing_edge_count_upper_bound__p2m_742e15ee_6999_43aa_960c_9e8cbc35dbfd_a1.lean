-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_upper_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:23:20.331602+00:00
-- url     : https://prove2.me/submissions/e89014e6-3155-4ca7-9c50-ab5cb288bfcd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_finset__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_finset_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  apply WilliamsonShmoys.planar_edge_bound_from_connected_finset_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
    M hV
  intro W hW hconn
  simpa using
    (WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
      (M.induce (W : Set V))
      (WilliamsonShmoys.planarDrawingOn_finset__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3 M hM W)
      hconn (by simpa using hW))