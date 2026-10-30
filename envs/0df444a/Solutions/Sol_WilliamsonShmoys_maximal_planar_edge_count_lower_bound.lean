-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:50:09.047602+00:00
-- url     : https://prove2.me/submissions/be47c275-f1c2-41de-9c50-ead04d1c0386

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hNe⟩ :=
    WilliamsonShmoys.planar_drawing_completion_edge_count M hM hV
  have hbound := hmax N hMN hN
  rw [hNe] at hbound
  exact hbound