-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:12:07.006747+00:00
-- url     : https://prove2.me/submissions/02e0d012-2fe1-4772-a0db-2132d0ea561f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono
import Theorems.Thm_WilliamsonShmoys_exists_maximal_of_finite_subgraph_closed

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V, H ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  have hmono :
      ∀ {A B : SimpleGraph V}, A ≤ B →
        WilliamsonShmoys.HasPlanarDrawingOn B →
          WilliamsonShmoys.HasPlanarDrawingOn A := by
    intro A B hAB hB
    exact WilliamsonShmoys.planarDrawingOn_mono hAB hB
  exact WilliamsonShmoys.exists_maximal_of_finite_subgraph_closed
    WilliamsonShmoys.HasPlanarDrawingOn hmono G hG