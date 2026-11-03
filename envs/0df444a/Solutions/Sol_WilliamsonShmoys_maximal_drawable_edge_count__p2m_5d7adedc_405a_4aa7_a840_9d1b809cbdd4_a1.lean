-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:43:12.488656+00:00
-- url     : https://prove2.me/submissions/9101999d-e213-4acb-99c9-306d4440548b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_977e0484_c39c_4e95_a5d4_5a834f8539e1_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      M <= N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N <= M) :
    letI : DecidableRel M.Adj := Classical.decRel M.Adj
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_977e0484_c39c_4e95_a5d4_5a834f8539e1_a1
      M hcard hM
  have hNM : N <= M := hmax N hMN hN
  have hEq : M = N := le_antisymm hMN hNM
  subst N
  simpa using hcount
