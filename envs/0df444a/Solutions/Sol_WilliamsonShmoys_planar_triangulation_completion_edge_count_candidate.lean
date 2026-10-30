-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:27:12.614846+00:00
-- url     : https://prove2.me/submissions/770315d5-a1ca-408a-bb15-46266f70bf82

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_completion__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.edge_maximal_planar_completion__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
      K hK
  have hcount :=
    WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
      L hV hL hmax
  exact ⟨L, hKL, hL, hcount⟩