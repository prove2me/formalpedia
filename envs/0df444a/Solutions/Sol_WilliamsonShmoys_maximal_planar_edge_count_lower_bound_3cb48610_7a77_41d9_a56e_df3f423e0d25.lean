-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:46:18.258201+00:00
-- url     : https://prove2.me/submissions/a2ab8d21-08d3-4231-b1f4-01cbf329f863

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_triangulation_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hRmax : ∀ S : SimpleGraph V,
      R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S = R)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ R.edgeSet.ncard + 6 := by
  obtain ⟨T, hRT, hTdraw, hTbound⟩ :=
    WilliamsonShmoys.maximal_planar_edge_count_triangulation_completion
      R hRdraw hCard
  have hTR : T = R := hRmax T hRT hTdraw
  rw [hTR] at hTbound
  exact hTbound