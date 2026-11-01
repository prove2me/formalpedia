-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:12:40.466199+00:00
-- url     : https://prove2.me/submissions/592d0109-3c52-456c-80a6-4be8183be7ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulation_edge_count__p2m_700bbd5b_00a3_4afe_b6e3_ec004e650a47_a1

set_option autoImplicit false

open scoped BigOperators

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hLcard⟩ :=
    WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count__p2m_700bbd5b_00a3_4afe_b6e3_ec004e650a47_a1
      K hcard hK
  have hLK : L ≤ K := hmax L hKL hL
  have hKLcard : K.edgeSet.ncard ≤ L.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hKL)
  have hLKcard : L.edgeSet.ncard ≤ K.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hLK)
  have hEq : K.edgeSet.ncard = L.edgeSet.ncard := le_antisymm hKLcard hLKcard
  rw [hEq]
  exact hLcard.symm