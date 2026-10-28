-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_71a098b3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:01:55.113193+00:00
-- url     : https://prove2.me/submissions/6b7a4862-9319-44db-8421-a79480f00c37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper K hK hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower K hK hmax hcard
  omega