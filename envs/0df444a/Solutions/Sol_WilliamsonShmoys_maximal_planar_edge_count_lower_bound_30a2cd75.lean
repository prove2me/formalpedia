-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_30a2cd75
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:31:59.645995+00:00
-- url     : https://prove2.me/submissions/06d3d696-75d9-44cd-95b0-1c0584448aff

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion_30a2cd75

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨T, hMT, hT, hE⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_completion_30a2cd75 M hM hV
  have hTM : T = M := hmax T hMT hT
  rw [hTM] at hE
  exact Nat.le_of_eq hE.symm