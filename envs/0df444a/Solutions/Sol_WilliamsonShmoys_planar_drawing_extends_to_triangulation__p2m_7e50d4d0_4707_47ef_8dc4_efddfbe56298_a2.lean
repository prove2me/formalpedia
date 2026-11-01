-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_7e50d4d0_4707_47ef_8dc4_efddfbe56298_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:34:11.159255+00:00
-- url     : https://prove2.me/submissions/210e20d5-3fa1-4899-9e6c-8b7df03ae385
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal__p2m_8d73f0a0_67f2_41e8_b5af_ed14b8bbe530_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8d73f0a0_67f2_41e8_b5af_ed14b8bbe530_a2
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
        L.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.finite_planar_supergraph_maximal__p2m_8d73f0a0_67f2_41e8_b5af_ed14b8bbe530_a2
      K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_8d73f0a0_67f2_41e8_b5af_ed14b8bbe530_a2
      L hL hcard hmax⟩