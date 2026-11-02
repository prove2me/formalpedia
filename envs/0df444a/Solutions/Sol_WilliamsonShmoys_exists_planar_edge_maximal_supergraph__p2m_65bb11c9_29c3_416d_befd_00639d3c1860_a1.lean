-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_maximal_supergraph__p2m_65bb11c9_29c3_416d_befd_00639d3c1860_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:55:24.605189+00:00
-- url     : https://prove2.me/submissions/a3e2a64a-3aa0-4976-8548-d256e396cf88

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_by_finite_choice__p2m_8945f9a8_f1f1_4069_b3b7_48c3e7c6f526_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    [DecidableRel P.Adj] :
    ∃ H : SimpleGraph V,
      P ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H) := by
  exact WilliamsonShmoys.exists_maximal_supergraph_by_finite_choice__p2m_8945f9a8_f1f1_4069_b3b7_48c3e7c6f526_a1
    P WilliamsonShmoys.HasPlanarDrawingOn hP