-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:41:50.378488+00:00
-- url     : https://prove2.me/submissions/b0183f20-0427-4320-b070-32dd6f77ec78

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hsub : ∀ u v, G.Adj u v → H.Adj u v) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  apply Set.ncard_mono
  apply SimpleGraph.edgeSet_mono
  intro u v huv
  exact hsub u v huv