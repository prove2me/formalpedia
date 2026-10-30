-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_1258d26f_3604_445e_9011_471047f5700d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:24:11.221202+00:00
-- url     : https://prove2.me/submissions/af1c1ff1-a413-4ee6-9eb0-9deeb07bd25b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_extension__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
      K hK
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
      H hH hMax hV
  have hMono :=
    WilliamsonShmoys.edgeSet_ncard_mono__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
      K H hKH
  omega