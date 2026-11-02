-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_triangulationCompletion__p2m_0824c1d6_466a_4e4b_9fa4_6bf9ba62d2e9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:31:39.653312+00:00
-- url     : https://prove2.me/submissions/89e783b2-a403-480e-a244-b2949c6c12d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeMaximalCompletion__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
import Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_edgeCount__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    ∃ K' : SimpleGraph V, K ≤ K' ∧ HasPlanarDrawingOn K' ∧
      (∀ [DecidableRel K'.Adj], K'.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨K', hsub, hdraw, hmax⟩ :=
    WilliamsonShmoys.planarDrawingOn_edgeMaximalCompletion__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
      K hK
  refine ⟨K', hsub, hdraw, ?_⟩
  intro inst
  exact WilliamsonShmoys.edgeMaximalPlanar_edgeCount__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
    K' hdraw hmax hn