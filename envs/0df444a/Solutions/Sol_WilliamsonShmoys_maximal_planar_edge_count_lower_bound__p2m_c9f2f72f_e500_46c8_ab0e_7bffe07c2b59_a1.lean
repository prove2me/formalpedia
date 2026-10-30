-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c9f2f72f_e500_46c8_ab0e_7bffe07c2b59_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:43:46.170048+00:00
-- url     : https://prove2.me/submissions/e6bb5dda-ad52-4ecd-9301-e448adb81ec7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound__p2m_cea2ff1b_6ac8_4e7a_9f09_37a536780796_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T →
      R ≤ T → T = R)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ R.edgeSet.ncard + 6 := by
  obtain ⟨T, hT, hRT, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_cea2ff1b_6ac8_4e7a_9f09_37a536780796_a2
      R hR hCard
  have hEq : T = R := hmax T hT hRT
  rw [hEq] at hcount
  exact hcount