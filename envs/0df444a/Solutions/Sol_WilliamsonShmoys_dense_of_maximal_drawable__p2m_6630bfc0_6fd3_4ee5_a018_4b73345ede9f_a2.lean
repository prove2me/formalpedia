-- Prove2me | solution 1 for WilliamsonShmoys.dense_of_maximal_drawable__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:03:28.591331+00:00
-- url     : https://prove2.me/submissions/fd587464-6e7b-4ed3-8a68-31e881bd6220

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_6f64e769_ed8d_4f23_84ce_0685c66257bc_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hMax : ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by
  have h := WilliamsonShmoys.maximal_drawable_edge_count__p2m_6f64e769_ed8d_4f23_84ce_0685c66257bc_a1 Q hDraw hMax hV
  omega