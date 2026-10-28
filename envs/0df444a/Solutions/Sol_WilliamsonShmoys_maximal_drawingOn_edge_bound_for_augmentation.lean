-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawingOn_edge_bound_for_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:09:28.909454+00:00
-- url     : https://prove2.me/submissions/fc9bd8cf-373a-4833-be7e-52da62003957
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count_for_maximal_drawing_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNdraw, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_edge_count_for_maximal_drawing_bound
      M hMdraw hCard
  have hEq : N = M := hMmax N hMN hNdraw
  subst N
  exact le_of_eq hCount