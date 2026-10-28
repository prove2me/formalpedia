-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_for_completion_91679e32
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:42:13.842081+00:00
-- url     : https://prove2.me/submissions/b3e15d72-6f1d-48d5-9de5-2205fb4ce88c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound
import Theorems.Thm_WilliamsonShmoys_planar_completion_three_edges

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hNplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hNmaximal : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_completion_three_edges N hNplanar hV
  have hKN : K ≤ N := hNmaximal K hNK hKplanar
  have hEq : N = K := le_antisymm hNK hKN
  rw [hEq]
  exact hKcount