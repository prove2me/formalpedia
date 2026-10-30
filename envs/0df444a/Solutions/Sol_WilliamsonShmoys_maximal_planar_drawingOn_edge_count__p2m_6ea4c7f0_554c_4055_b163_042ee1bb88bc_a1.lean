-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:40:27.327367+00:00
-- url     : https://prove2.me/submissions/4958b0ed-26ea-4705-9dc4-75811b0dc175

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeSet = K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  let m := 3 * Fintype.card V - 6
  have hUpper := WilliamsonShmoys.planar_edge_count_upper__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1 H hH hCard
  have hNotLt : ¬ H.edgeSet.ncard < m := by
    intro hlt
    obtain ⟨K, hStrict, hK⟩ := WilliamsonShmoys.planar_edge_augmentation__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1 H hH hCard hlt
    have hEq := hMax K hStrict.subset hK
    exact hStrict.ne hEq
  have hm : H.edgeSet.ncard = m := by omega
  dsimp [m] at hm
  omega