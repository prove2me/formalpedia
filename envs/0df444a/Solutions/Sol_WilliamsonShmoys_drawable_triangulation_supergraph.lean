-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:49:06.285578+00:00
-- url     : https://prove2.me/submissions/4bf6df8a-5f83-4a3a-b3ea-a1491a7c164a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_supergraph_choose_max_v2
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_supergraph_maximal_count_v2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hdraw : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hKL, hLdraw, hmaxK⟩ :=
    WilliamsonShmoys.drawable_triangulation_supergraph_choose_max_v2 K hdraw
  refine ⟨L, hKL, hLdraw, ?_⟩
  apply WilliamsonShmoys.drawable_triangulation_supergraph_maximal_count_v2
      L hLdraw hV
  intro M hLM hMdraw
  exact hmaxK M (hKL.trans hLM) hMdraw