-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_200a044f_248b_4fd0_bcd3_c7e9d499ee78
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:11:45.459984+00:00
-- url     : https://prove2.me/submissions/0ebf2f87-7e20-4bcd-bea9-50e02c61be90

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_nat_edge_count_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hU, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_nat_edge_count_completion T hT hCard
  have hUT : U = T := hmax U hTU hU
  rw [hUT] at hcount
  exact hcount.symm