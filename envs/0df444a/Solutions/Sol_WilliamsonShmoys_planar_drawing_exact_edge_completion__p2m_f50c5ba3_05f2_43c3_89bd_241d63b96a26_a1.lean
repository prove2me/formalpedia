-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_exact_edge_completion__p2m_f50c5ba3_05f2_43c3_89bd_241d63b96a26_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:46:44.84345+00:00
-- url     : https://prove2.me/submissions/a7b66214-f026-4e2b-b925-fe0ab44f6149
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_is_maximal__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       3 * Fintype.card V - 6 = H.edgeFinset.card) := by
  obtain ⟨H, hGH, hHplanar, hHmax⟩ :=
    WilliamsonShmoys.planar_completion_is_maximal__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
      G hcard hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
      H hcard hHplanar hHmax
  exact ⟨H, hGH, hHplanar, hcount⟩