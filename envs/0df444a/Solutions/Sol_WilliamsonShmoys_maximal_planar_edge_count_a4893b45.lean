-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_a4893b45
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:29:24.708595+00:00
-- url     : https://prove2.me/submissions/980c85f5-2a51-4488-81f6-50ab62d20f0c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count

set_option autoImplicit false

/-- Exact reduction: maximality identifies K with a drawable supergraph that has the planar edge bound with equality. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count K hK hV
  have hLK : L = K := hMax L hKL hL
  rw [← hLK]
  exact hCount