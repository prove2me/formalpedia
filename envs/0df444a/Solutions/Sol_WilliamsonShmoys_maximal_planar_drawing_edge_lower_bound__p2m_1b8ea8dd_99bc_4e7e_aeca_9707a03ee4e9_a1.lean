-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:56:58.939163+00:00
-- url     : https://prove2.me/submissions/ba8f3748-c9ea-4e94-ae89-ced512307077
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_lower_bound__p2m_0cd4b9a1_dcab_4b06_b6ad_2748a36b5bdf_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = H.edgeSet) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hSub, hKDraw, hBound⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound__p2m_0cd4b9a1_dcab_4b06_b6ad_2748a36b5bdf_a1
      H hDraw hV
  have hEq : K.edgeSet = H.edgeSet := hMax K hSub hKDraw
  rw [hEq] at hBound
  exact hBound