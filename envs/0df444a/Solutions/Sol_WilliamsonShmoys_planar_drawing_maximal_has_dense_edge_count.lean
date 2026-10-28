-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_has_dense_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:00:34.736469+00:00
-- url     : https://prove2.me/submissions/691a3c97-d6a7-4d75-b9c6-21421ada8cfb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_dense_planar_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hcard⟩ :=
    WilliamsonShmoys.exists_dense_planar_supergraph K hV hK
  have hLK : L ≤ K := hmax L hKL hL
  have heq : K = L := le_antisymm hKL hLK
  rw [heq]
  omega