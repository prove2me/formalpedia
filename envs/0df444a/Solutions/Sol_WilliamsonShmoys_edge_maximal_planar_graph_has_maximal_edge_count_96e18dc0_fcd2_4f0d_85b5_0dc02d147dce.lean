-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_has_maximal_edge_count_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:42:12.059733+00:00
-- url     : https://prove2.me/submissions/0b853b80-51b2-47bd-abc8-ce82359219ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_can_be_completed_to_triangulation

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      J.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hSub, hJ, hCount⟩ :=
    WilliamsonShmoys.planar_graph_can_be_completed_to_triangulation H hH hCard
  have hEq : J.edgeSet = H.edgeSet := hMaximal J hSub hJ
  rw [← hEq]
  exact hCount