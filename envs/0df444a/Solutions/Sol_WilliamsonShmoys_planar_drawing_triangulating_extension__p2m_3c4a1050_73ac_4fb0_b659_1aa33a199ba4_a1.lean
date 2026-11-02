-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulating_extension__p2m_3c4a1050_73ac_4fb0_b659_1aa33a199ba4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:58:29.578098+00:00
-- url     : https://prove2.me/submissions/072ba23a-c906-45e1-9085-a9223225815e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_4c570e3e_7abb_4bee_95ce_463a755b298b_a2
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing__p2m_4c570e3e_7abb_4bee_95ce_463a755b298b_a2

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V - 6 = H.edgeFinset.card := by
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
  obtain ⟨H, hGH, hdrawH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4c570e3e_7abb_4bee_95ce_463a755b298b_a2
      G hdraw
  have hcount :=
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_4c570e3e_7abb_4bee_95ce_463a755b298b_a2
      (V := V) hcard H hdrawH hmax
  exact ⟨H, hGH, hdrawH, hcount⟩