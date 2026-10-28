-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_maximal_by_inclusion_16efa91f_ea17_4fca_8681_329f091064c3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:42:43.111128+00:00
-- url     : https://prove2.me/submissions/35d62e64-72f0-4294-b42e-eb9138e6583c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V, L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      forall N : SimpleGraph V, M <= N ->
        WilliamsonShmoys.HasPlanarDrawingOn N -> N = M := by
  exact WilliamsonShmoys.exists_maximal_supergraph
    L WilliamsonShmoys.HasPlanarDrawingOn hL