-- Prove2me | solution 1 for WilliamsonShmoys.planarTriangulatedExtensionCardinality__p2m_fdcf6722_88f2_45ca_bb18_4e42aed9226b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:29:57.664741+00:00
-- url     : https://prove2.me/submissions/38b336e2-2566-4ba5-8e47-2046f9e9318e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximalPlanarExtension__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
import Theorems.Thm_WilliamsonShmoys_maximalPlanarEdgeCount__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N ∧
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       M.edgeFinset ⊆ N.edgeFinset) ∧
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       N.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨N, dN, hN, hMN, hmax⟩ :=
    WilliamsonShmoys.maximalPlanarExtension__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
      M dM hM hn
  obtain hcount :=
    WilliamsonShmoys.maximalPlanarEdgeCount__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
      N dN hN hn hmax
  exact ⟨N, dN, hN, hMN, hcount⟩