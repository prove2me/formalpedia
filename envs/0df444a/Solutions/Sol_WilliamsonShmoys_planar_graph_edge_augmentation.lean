-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:30:54.63245+00:00
-- url     : https://prove2.me/submissions/a2caaafc-b65b-41eb-a1c6-53929e9af2e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_on_fixed_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_on_fixed_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hdeficit : U.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧ W ≠ U ∧ WilliamsonShmoys.HasPlanarDrawingOn W := by
  classical
  obtain ⟨M, hUM, hM, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_on_fixed_vertices U hU
  by_contra hnot
  have hMU : M = U := by
    by_contra hne
    exact hnot ⟨M, hUM, hne, hM⟩
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound_on_fixed_vertices M hV hM hmax
  rw [hMU] at hbound
  exact (Nat.not_lt_of_ge hbound) hdeficit