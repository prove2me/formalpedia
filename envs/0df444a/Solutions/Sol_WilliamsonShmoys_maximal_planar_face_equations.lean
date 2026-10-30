-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_equations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:22:17.592291+00:00
-- url     : https://prove2.me/submissions/906bb304-739b-4147-a81d-db705d7ee073

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hE := WilliamsonShmoys.maximal_planar_edge_count_euler
    L hL hMax hCard
  refine ⟨2 * Fintype.card V - 4, ?_⟩
  omega