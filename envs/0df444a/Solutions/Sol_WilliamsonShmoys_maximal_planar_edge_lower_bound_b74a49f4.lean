-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_b74a49f4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:00:38.119303+00:00
-- url     : https://prove2.me/submissions/aa79b1d0-9fac-433f-85f9-6837b6c62488
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count_3c24a379

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hEdges⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_edge_count_3c24a379 K hK hCard
  have hLK : L = K := hmax L hKL hL
  rw [hLK] at hEdges
  exact hEdges.le