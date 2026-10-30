-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_triangulation_extension__p2m_f0b6b169_74af_4776_af38_cf20fc29acd0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:19:28.005669+00:00
-- url     : https://prove2.me/submissions/b9e58fc0-91a5-4804-9bdc-a31cd6eadf0c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_extension__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_with_drawing__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a2

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧ HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmaximal⟩ :=
    WilliamsonShmoys.finite_maximal_planar_extension__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a1
      K hK hV
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_count_with_drawing__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a2
      L hL hV hmaximal⟩