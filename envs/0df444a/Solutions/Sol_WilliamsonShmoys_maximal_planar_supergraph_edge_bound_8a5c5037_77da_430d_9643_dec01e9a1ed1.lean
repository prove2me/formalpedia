-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_bound_8a5c5037_77da_430d_9643_dec01e9a1ed1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:19:22.101188+00:00
-- url     : https://prove2.me/submissions/d457714b-aab8-4c94-bce9-19556b471722
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet ⊆ K.edgeSet) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hcard⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_has_triangulation K hK hV
  have hLK := hmax L hKL hL
  have hsets : K.edgeSet = L.edgeSet := Set.Subset.antisymm hKL hLK
  have hnc : K.edgeSet.ncard = L.edgeSet.ncard := congrArg Set.ncard hsets
  rw [hnc, hcard]