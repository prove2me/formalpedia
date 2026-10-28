-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_for_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:30:51.602628+00:00
-- url     : https://prove2.me/submissions/1f04b1ff-1404-42a8-af78-892739d6498b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_completion_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.exists_planar_completion_exact_edge_count K hK hCard
  have hLK : L ≤ K := hMax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  rw [hEq] at hCount
  exact hCount