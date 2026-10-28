-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension_for_maximal_edge_bound_50a3c5c3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:44:06.069272+00:00
-- url     : https://prove2.me/submissions/bd078ac0-17c0-47e5-abaa-380bdc913b98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_50a3c5c3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_50a3c5c3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨Q, hPQ, hQdraw, hQmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_50a3c5c3 P hPdraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_50a3c5c3 Q hQdraw hCard hQmax
  exact ⟨Q, hPQ, hQdraw, hCount⟩