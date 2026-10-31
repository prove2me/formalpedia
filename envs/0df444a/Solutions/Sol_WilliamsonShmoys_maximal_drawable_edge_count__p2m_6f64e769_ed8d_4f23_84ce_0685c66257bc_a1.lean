-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_6f64e769_ed8d_4f23_84ce_0685c66257bc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:16:41.672394+00:00
-- url     : https://prove2.me/submissions/e2b311e9-90aa-445f-85be-204bdce61bb7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_upper_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q)
    (hMax : ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q)
    (hV : 3 ≤ Fintype.card V) : Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.maximal_drawable_edge_count_upper_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1 Q hDraw hV
  have hLower := WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1 Q hDraw hMax hV
  omega