-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanar_edge_card__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:19:13.012792+00:00
-- url     : https://prove2.me/submissions/136bfe96-2999-4211-8adb-6ed0ed7bd6d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_triangulationCompletion__p2m_0824c1d6_466a_4e4b_9fa4_6bf9ba62d2e9_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ K' : SimpleGraph V, K ≤ K' → HasPlanarDrawingOn K' → K' = K)
    (hn : 3 ≤ Fintype.card V) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨K', hKK', hK', hcard⟩ :=
    WilliamsonShmoys.planarDrawingOn_triangulationCompletion__p2m_0824c1d6_466a_4e4b_9fa4_6bf9ba62d2e9_a1
      K hK hn
  have heq : K' = K := hmax K' hKK' hK'
  subst K'
  exact hcard