-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_maximal_planar_drawing_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:20:49.272522+00:00
-- url     : https://prove2.me/submissions/eba79712-9848-4a07-a70f-3c8f70c892d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_for_edge_bound_v2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hPmax : ∀ Q : SimpleGraph V,
      P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ P) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hQdraw, hQcard⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph_for_edge_bound_v2
      P hV hPdraw
  have hQP : Q ≤ P := hPmax Q hPQ hQdraw
  have hQeq : Q = P := le_antisymm hQP hPQ
  rw [← hQeq]
  omega