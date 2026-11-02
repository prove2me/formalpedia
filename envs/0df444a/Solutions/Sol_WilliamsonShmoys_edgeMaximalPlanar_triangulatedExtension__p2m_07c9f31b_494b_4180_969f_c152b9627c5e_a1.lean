-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximalPlanar_triangulatedExtension__p2m_07c9f31b_494b_4180_969f_c152b9627c5e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:13:35.777752+00:00
-- url     : https://prove2.me/submissions/404a4853-b75a-4238-88a5-e718943a10a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_inclusionMaximalPlanarSupergraph__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
import Theorems.Thm_WilliamsonShmoys_inclusionMaximalPlanarSupergraph_has_maxEdges__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      K ≤ H ∧ HasPlanarDrawingOn H ∧
        3 * Fintype.card V - 6 = H.edgeFinset.card := by
  obtain ⟨H, hHdec, hKH, hHplanar, hmax⟩ :=
    WilliamsonShmoys.exists_inclusionMaximalPlanarSupergraph__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
      K hK
  refine ⟨H, hHdec, hKH, hHplanar, ?_⟩
  letI : DecidableRel H.Adj := hHdec
  exact WilliamsonShmoys.inclusionMaximalPlanarSupergraph_has_maxEdges__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
    H hHplanar hn hmax