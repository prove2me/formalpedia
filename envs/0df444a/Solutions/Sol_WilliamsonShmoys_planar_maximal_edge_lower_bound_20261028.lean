-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_lower_bound_20261028
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:49:54.441546+00:00
-- url     : https://prove2.me/submissions/501d3308-a9e0-438c-95ab-b557d9fa3095
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count_20261028

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.planar_supergraph_exact_edge_count_20261028 K hK hCard
  have hLK : L ≤ K := hMax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  rw [← hEq]
  exact Nat.le_of_eq hCount.symm