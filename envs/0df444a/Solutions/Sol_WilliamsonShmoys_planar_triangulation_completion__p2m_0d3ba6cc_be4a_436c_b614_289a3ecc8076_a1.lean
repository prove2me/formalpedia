-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_0d3ba6cc_be4a_436c_b614_289a3ecc8076_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:02:32.626991+00:00
-- url     : https://prove2.me/submissions/09aa69c2-c1f9-4fc0-bd84-b849ee162d6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hHplanar, hHmax⟩ :=
    WilliamsonShmoys.finite_planar_supergraph_maximal__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
      K hK
  refine ⟨H, hKH, hHplanar, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
    H hCard hHplanar hHmax
