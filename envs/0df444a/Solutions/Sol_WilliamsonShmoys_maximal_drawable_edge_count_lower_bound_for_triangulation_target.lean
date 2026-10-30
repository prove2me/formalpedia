-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_for_triangulation_target
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:06:04.747525+00:00
-- url     : https://prove2.me/submissions/1fc48acb-a7ac-4312-839b-92238cf50fa1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_for_edge_count_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ L : SimpleGraph V, M ≤ L → HasPlanarDrawingOn L → L ≤ M)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨L, hML, hL, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_extension_for_edge_count_bound
      M hM hCard
  have hLM : L ≤ M := hmax L hML hL
  have hEq : L = M := le_antisymm hLM hML
  rw [hEq] at hCount
  exact le_of_eq hCount.symm