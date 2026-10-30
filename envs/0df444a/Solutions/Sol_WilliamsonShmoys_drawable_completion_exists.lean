-- Prove2me | solution 1 for WilliamsonShmoys.drawable_completion_exists
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:15:49.137429+00:00
-- url     : https://prove2.me/submissions/246358ec-3767-4195-b627-a2b91247da2d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_completion_maximal_extension_v2
import Theorems.Thm_WilliamsonShmoys_drawable_completion_maximal_edge_count_v2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    exists N : SimpleGraph V,
      (forall {u v}, M.Adj u v -> N.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hdrawN, hmax⟩ :=
    WilliamsonShmoys.drawable_completion_maximal_extension_v2 M hM hV
  refine ⟨N, hMN, hdrawN, ?_⟩
  exact WilliamsonShmoys.drawable_completion_maximal_edge_count_v2 N hdrawN hmax hV