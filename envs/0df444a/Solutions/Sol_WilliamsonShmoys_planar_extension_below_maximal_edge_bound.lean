-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_below_maximal_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:34:41.652946+00:00
-- url     : https://prove2.me/submissions/348b52fe-4a8e-421a-8a0a-01329bae3683
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_exists_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_extension_edge_lower_bound_of_maximal_drawable

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hE : U.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ W : SimpleGraph V, U ≤ W ∧ ¬ W ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn W := by
  classical
  obtain ⟨W, hUW, hW, hmax⟩ :=
    WilliamsonShmoys.planar_extension_exists_maximal_drawable_supergraph U hU
  refine ⟨W, hUW, ?_, hW⟩
  intro hWU
  have hEq : W = U := le_antisymm hWU hUW
  subst W
  have hbound :=
    WilliamsonShmoys.planar_extension_edge_lower_bound_of_maximal_drawable U hV hU hmax
  omega