-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_ctx816e1e7a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:40:02.921095+00:00
-- url     : https://prove2.me/submissions/2a111140-1d3e-4e5f-a074-5f0f44f621c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_ctx816e1e7
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : forall U : SimpleGraph V, W < U -> Not (WilliamsonShmoys.HasPlanarDrawingOn U)) :
    3 * Fintype.card V <= W.edgeSet.ncard + 6 := by
  obtain ⟨Q, hWQ, hQplanar, hQcount⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_ctx816e1e7 (W := W) hV hW
  have hnot : Not (W < Q) := fun hlt => hmax Q hlt hQplanar
  have hQW : Q <= W := by
    by_contra hnotQW
    have hne : Not (W = Q) := by
      intro heq
      apply hnotQW
      rw [← heq]
    exact hnot (lt_of_le_of_ne hWQ hne)
  have heq : Q = W := le_antisymm hQW hWQ
  rw [← heq]
  omega