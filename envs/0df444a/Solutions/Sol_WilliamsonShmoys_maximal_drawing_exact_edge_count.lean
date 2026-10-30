-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:00:01.421213+00:00
-- url     : https://prove2.me/submissions/83d283ac-5740-4713-b485-5c7977ca39f9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_with_triangulated_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hTdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hTmax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hTK, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.planar_drawing_completion_with_triangulated_edge_count
      T hTdraw hCard
  have hKT : K ≤ T := hTmax K hTK hKdraw
  have hEq : K = T := le_antisymm hKT hTK
  have hTcount : (T.edgeSet.ncard : Int) =
      3 * (Fintype.card V : Int) - 6 := by
    simpa [hEq] using hKcount
  omega
