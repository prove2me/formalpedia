-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:12.565729+00:00
-- url     : https://prove2.me/submissions/47d00ed8-2ef7-4b09-bbd1-c388358d19c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulated_edge_count__p2m_eba63f99_4b89_43c7_9979_04802f4e758b_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W = U) :
    (letI : DecidableRel U.Adj := Classical.decRel U.Adj
     U.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨W, hUW, hW, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_triangulated_edge_count__p2m_eba63f99_4b89_43c7_9979_04802f4e758b_a1
      U hU hcard
  have hWU : W = U := hmax W hUW hW
  subst W
  exact hcount