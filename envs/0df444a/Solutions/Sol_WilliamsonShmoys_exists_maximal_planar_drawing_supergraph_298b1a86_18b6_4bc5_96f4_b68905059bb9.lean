-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_298b1a86_18b6_4bc5_96f4_b68905059bb9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:20:04.095858+00:00
-- url     : https://prove2.me/submissions/a27cb9b5-c328-4c09-91c7-df642f861558

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDrawing : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_predicate
    (fun G => HasPlanarDrawingOn G) M hDrawing