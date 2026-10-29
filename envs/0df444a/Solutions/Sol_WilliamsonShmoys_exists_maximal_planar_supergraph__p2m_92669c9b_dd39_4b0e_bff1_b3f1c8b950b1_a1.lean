-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:51:11.368994+00:00
-- url     : https://prove2.me/submissions/cc609e3b-7cc9-4fab-a0c0-bdd98a4ce469

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_supergraph_maximal_for_predicate__p2m_c813e8d9_188c_4202_b644_d7aaf9123e11_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V,
        Set.Subset N.edgeSet P.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn P →
        Set.Subset P.edgeSet N.edgeSet := by
  exact WilliamsonShmoys.exists_supergraph_maximal_for_predicate__p2m_c813e8d9_188c_4202_b644_d7aaf9123e11_a1
    M WilliamsonShmoys.HasPlanarDrawingOn hM