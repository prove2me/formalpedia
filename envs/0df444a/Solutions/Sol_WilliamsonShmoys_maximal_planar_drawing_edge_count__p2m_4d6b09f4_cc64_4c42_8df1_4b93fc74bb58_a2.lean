-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:48.668206+00:00
-- url     : https://prove2.me/submissions/ed4d1475-4afd-49f6-aa8f-65d96057fcd2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper__p2m_1095f796_c580_4096_843f_cd051f083539_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_1095f796_c580_4096_843f_cd051f083539_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_1095f796_c580_4096_843f_cd051f083539_a1
      K hV hK
  have hLower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_1095f796_c580_4096_843f_cd051f083539_a1
      K hV hK hMax
  omega