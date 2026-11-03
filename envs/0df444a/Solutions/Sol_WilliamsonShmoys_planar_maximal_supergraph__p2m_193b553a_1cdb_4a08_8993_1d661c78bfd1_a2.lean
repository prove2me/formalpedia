-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:51:12.742387+00:00
-- url     : https://prove2.me/submissions/077738a3-d3e8-4bd3-94be-808bf4984137

import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      Exists fun dK : DecidableRel K.Adj =>
        And (H.edgeFinset ⊆ K.edgeFinset)
          (And (WilliamsonShmoys.HasPlanarDrawingOn K)
            (forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
              K.edgeFinset ⊆ L.edgeFinset ->
              WilliamsonShmoys.HasPlanarDrawingOn L ->
              L.edgeFinset = K.edgeFinset)) :=
  WilliamsonShmoys.planar_maximal_supergraph__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3 H dH hH hcard