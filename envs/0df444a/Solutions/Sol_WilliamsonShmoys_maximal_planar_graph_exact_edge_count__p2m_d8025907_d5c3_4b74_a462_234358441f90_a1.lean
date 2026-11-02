-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:42:31.961224+00:00
-- url     : https://prove2.me/submissions/a6cf8aba-6f5b-4be3-8ec7-2e73d12f4605
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_upper_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset = L.edgeFinset) :
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.maximal_planar_upper_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2 L dL hL hn
  have hlower := WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2 L dL hL hn hmax
  omega