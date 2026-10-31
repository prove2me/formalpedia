-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:07:07.473554+00:00
-- url     : https://prove2.me/submissions/5e23aac1-aabd-4841-a3eb-b6bc5ab64c54

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_9a006411_f424_41be_bae2_b9a9d8f6aac6_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hMK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_9a006411_f424_41be_bae2_b9a9d8f6aac6_a1
      M hM hV
  have hKM : K.edgeSet ⊆ M.edgeSet := hMax K hMK hK
  have hEq : M.edgeSet = K.edgeSet := Set.Subset.antisymm hMK hKM
  simpa [hEq] using hcount