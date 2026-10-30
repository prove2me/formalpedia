-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:09:38.823136+00:00
-- url     : https://prove2.me/submissions/87ec692e-a346-49e8-859b-0af70dcee490

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_edge_bound_a9d6da29_ff69_465c_9a71_ac972a1190c4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V)
    (hmax : forall R : SimpleGraph V,
      M <= R ->
      WilliamsonShmoys.HasPlanarDrawingOn R ->
      R <= M) :
    3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
  obtain ⟨T, hMT, hTplanar, hTcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension_edge_bound_a9d6da29_ff69_465c_9a71_ac972a1190c4 M hM hV
  have hTM : T <= M := hmax T hMT hTplanar
  have hEq : T = M := le_antisymm hTM hMT
  rw [← hEq]
  exact le_of_eq hTcount.symm