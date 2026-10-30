-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_eq_of_maximal_planar_drawing_f3620a14
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:57:30.715108+00:00
-- url     : https://prove2.me/submissions/9dcba007-5862-47e6-bb3f-06591c14b48a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_card_upper_bound_f3620a14
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_card_lower_bound_f3620a14

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R → S ≤ R → R ≤ S) :
    S.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_drawing_edge_card_upper_bound_f3620a14 S hS hCard
  · exact WilliamsonShmoys.maximal_planar_drawing_edge_card_lower_bound_f3620a14
      S hS hCard hmax