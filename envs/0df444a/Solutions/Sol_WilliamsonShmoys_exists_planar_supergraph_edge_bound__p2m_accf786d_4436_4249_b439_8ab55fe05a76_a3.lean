-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_edge_bound__p2m_accf786d_4436_4249_b439_8ab55fe05a76_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T05:35:17.739327+00:00
-- url     : https://prove2.me/submissions/2c3bd056-95d9-42c5-8b74-177e6c4c4a84

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      And (LE.le L.edgeSet M.edgeSet)
        (And (WilliamsonShmoys.HasPlanarDrawingOn M)
          (LE.le (3 * Fintype.card V) (M.edgeSet.ncard + 6))) := by
  cases WilliamsonShmoys.maximal_planar_supergraph__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a2
      L hLplanar with
  | intro M witness =>
    cases witness with
    | intro hLM witness =>
      cases witness with
      | intro hMplanar hmax =>
        exact Exists.intro M
          (And.intro hLM
            (And.intro hMplanar
              (WilliamsonShmoys.maximal_planar_edge_bound__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a2
                M hV hMplanar hmax)))