-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:50:10.023356+00:00
-- url     : https://prove2.me/submissions/18179566-5597-4b91-b747-6555ac3a4a16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_supergraph_of_property__p2m_8a206f96_b3dd_4ad6_9517_cbf07b9eb0ad_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ M.edgeSet := by
  exact WilliamsonShmoys.exists_edge_maximal_supergraph_of_property__p2m_8a206f96_b3dd_4ad6_9517_cbf07b9eb0ad_a1
    WilliamsonShmoys.HasPlanarDrawingOn N hN