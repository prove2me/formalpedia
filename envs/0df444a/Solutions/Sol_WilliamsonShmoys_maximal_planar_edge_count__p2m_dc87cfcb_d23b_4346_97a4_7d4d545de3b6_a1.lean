-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:05.435147+00:00
-- url     : https://prove2.me/submissions/806b252d-aed5-4a32-8d36-2af08ad27e1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_upper_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hMax : ∀ G : SimpleGraph V, HasPlanarDrawingOn G → H ≤ G → G ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.maximal_planar_upper_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1
      H hH hV
  have hLower :=
    WilliamsonShmoys.maximal_planar_lower_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1
      H hH hV hMax
  omega