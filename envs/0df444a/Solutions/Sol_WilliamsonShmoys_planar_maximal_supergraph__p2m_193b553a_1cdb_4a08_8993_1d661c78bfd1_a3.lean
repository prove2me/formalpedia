-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:58:45.097706+00:00
-- url     : https://prove2.me/submissions/10da98d8-3d4b-4707-bf80-1a0f7145ff87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate__p2m_ef9f633b_8271_42d9_b073_b93d60169594_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        K.edgeFinset ⊆ L.edgeFinset →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeFinset = K.edgeFinset := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_ef9f633b_8271_42d9_b073_b93d60169594_a1
    (fun G => WilliamsonShmoys.HasPlanarDrawingOn G) H dH hH