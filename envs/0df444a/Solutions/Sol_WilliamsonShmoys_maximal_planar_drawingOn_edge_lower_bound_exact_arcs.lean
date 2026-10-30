-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_lower_bound_exact_arcs
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:29:23.038764+00:00
-- url     : https://prove2.me/submissions/13b27936-d891-41f0-b678-762aaa579e5e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_augmentation_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hU, hbound⟩ :=
    WilliamsonShmoys.planar_drawingOn_augmentation_edge_bound T hV hT
  have hUT : U ≤ T := hmax U hTU hU
  have hEq : U = T := le_antisymm hUT hTU
  rw [hEq] at hbound
  exact hbound