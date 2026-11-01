-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:29:50.378593+00:00
-- url     : https://prove2.me/submissions/201cbe62-c77a-4da2-b58d-d89e5d9d3e4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_dense_planar_supergraph__p2m_4762f418_9ea4_4d75_92d4_167b1519faba_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hBound⟩ :=
    WilliamsonShmoys.exists_dense_planar_supergraph__p2m_4762f418_9ea4_4d75_92d4_167b1519faba_a1
      H hCard hH
  have hEq : K = H := hMax K hHK hK
  rw [hEq] at hBound
  exact hBound