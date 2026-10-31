-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_embedding_face_counts__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:58:50.645354+00:00
-- url     : https://prove2.me/submissions/95259270-0b31-4f17-b3ae-d41ca639b977

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_embedding_edge_count__p2m_a731e400_b1bb_4df1_b39d_695b2e00a6cf_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn T) (hV : 3 <= Fintype.card V)
    (hMax : forall N : SimpleGraph V, T <= N -> HasPlanarDrawingOn N -> N <= T) :
    Exists fun f : Nat => And (Fintype.card V + f = T.edgeSet.ncard + 2)
      (3 * f = 2 * T.edgeSet.ncard) := by
  have hE := WilliamsonShmoys.maximal_planar_embedding_edge_count__p2m_a731e400_b1bb_4df1_b39d_695b2e00a6cf_a1
    T hDraw hV hMax
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega