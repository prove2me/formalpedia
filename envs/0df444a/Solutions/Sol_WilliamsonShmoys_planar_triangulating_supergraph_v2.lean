-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulating_supergraph_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:12:13.731828+00:00
-- url     : https://prove2.me/submissions/92ac3980-1324-446b-95db-05bb87c80197
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_b456ae06_v4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_b456ae06_v4

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_b456ae06_v4 H hV hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count_b456ae06_v4 K hV hK hmax⟩