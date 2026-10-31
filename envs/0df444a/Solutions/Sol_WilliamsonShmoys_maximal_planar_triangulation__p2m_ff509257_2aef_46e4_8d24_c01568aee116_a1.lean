-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation__p2m_ff509257_2aef_46e4_8d24_c01568aee116_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:21:02.561221+00:00
-- url     : https://prove2.me/submissions/aa87271c-2b9e-4f64-ab1e-f1ae6e5244fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) :
    ∃ T : SimpleGraph V,
      HasPlanarDrawingOn T ∧ H ≤ T ∧
        T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hT, hHT, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1
      H hH hV
  refine ⟨T, hT, hHT, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1
    T hT hV hmax