-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:41:23.181871+00:00
-- url     : https://prove2.me/submissions/8355d4e1-fbf1-4ca1-bfd4-40044cbb1ab1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P Q : SimpleGraph V) (hPQ : P.edgeSet ⊆ Q.edgeSet) :
    P.edgeSet.ncard ≤ Q.edgeSet.ncard := by
  exact Set.ncard_le_ncard hPQ (Set.finite_univ.subset (by
    intro e he
    exact Set.mem_univ e))