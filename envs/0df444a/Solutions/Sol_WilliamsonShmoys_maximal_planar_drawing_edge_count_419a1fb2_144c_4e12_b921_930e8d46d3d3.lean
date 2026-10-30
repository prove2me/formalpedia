-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:03:57.81183+00:00
-- url     : https://prove2.me/submissions/e142cd9e-c2fd-471d-a94e-06857f1d0e37

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_for_maximal_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall N : SimpleGraph V, M <= N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N <= M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨K, hMK, hK, hKcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_for_maximal_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3 M hM hCard
  have hKM : K <= M := hMax K hMK hK
  have hEq : K = M := le_antisymm hKM hMK
  rw [← hEq]
  exact hKcard