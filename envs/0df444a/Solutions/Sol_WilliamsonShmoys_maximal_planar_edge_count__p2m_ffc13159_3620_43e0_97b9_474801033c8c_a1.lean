-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:41:18.477342+00:00
-- url     : https://prove2.me/submissions/c76b7d6d-0431-4377-89c8-8118e70bacdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1 L hDraw hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1 L hDraw hV hMax
  omega