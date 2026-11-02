-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_9bfda91a_9bda_408b_a2fd_6ab368fb7e28_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:50:18.145747+00:00
-- url     : https://prove2.me/submissions/1a1097be-4e09-48b9-8ff2-60128650940a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_downward_closed__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V, L.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      (∀ J : SimpleGraph V, K.edgeSet ⊆ J.edgeSet →
        HasPlanarDrawingOn J → J.edgeSet ⊆ K.edgeSet) := by
  have hdown : ∀ {G H : SimpleGraph V}, G.edgeSet ⊆ H.edgeSet →
      HasPlanarDrawingOn H → HasPlanarDrawingOn G :=
    WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
  exact WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
    HasPlanarDrawingOn hdown L hplanar