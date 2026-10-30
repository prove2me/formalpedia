-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_strict_of_added_adj__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:22.577791+00:00
-- url     : https://prove2.me/submissions/073a5d50-f333-48f0-8bdb-84c427c82821

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K M : SimpleGraph V)
    (hsub : K.edgeSet ⊆ M.edgeSet)
    {u v : V}
    (hMuv : M.Adj u v)
    (huv : ¬ K.Reachable u v) :
    ¬ M.edgeSet ⊆ K.edgeSet := by
  intro hMsubsetK
  have hKuv : K.Adj u v := by
    apply K.mem_edgeSet.mp
    exact hMsubsetK (M.mem_edgeSet.mpr hMuv)
  exact huv (SimpleGraph.Adj.reachable hKuv)