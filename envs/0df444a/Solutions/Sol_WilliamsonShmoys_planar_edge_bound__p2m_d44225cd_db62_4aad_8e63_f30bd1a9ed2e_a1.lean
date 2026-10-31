-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:34:35.021998+00:00
-- url     : https://prove2.me/submissions/a733f057-1b9b-4c82-bdf7-51561406c0cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1 K hK
  have hExact :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1 H hH hV hMax
  have hCard : K.edgeSet.ncard <= H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hKH)
  omega