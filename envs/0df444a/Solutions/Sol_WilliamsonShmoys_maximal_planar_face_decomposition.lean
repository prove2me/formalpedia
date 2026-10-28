-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:20:01.456393+00:00
-- url     : https://prove2.me/submissions/d4284992-4296-4177-87ce-a98933529999
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_formula
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangular_face_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.maximal_planar_euler_formula L hL hMax hCard
  exact ⟨f, hEuler,
    WilliamsonShmoys.maximal_planar_triangular_face_count L hL hMax hCard f hEuler⟩