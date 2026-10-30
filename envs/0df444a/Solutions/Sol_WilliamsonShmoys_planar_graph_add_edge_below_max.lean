-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_add_edge_below_max
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:41:39.326567+00:00
-- url     : https://prove2.me/submissions/694eeecd-fe1c-4d1f-931d-72c414d1788d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite_choice
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_via_euler

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hSmall : R.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ S : SimpleGraph V, R < S ∧ WilliamsonShmoys.HasPlanarDrawingOn S := by
  obtain ⟨S, hRS, hSdraw, hSmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_finite_choice R hRdraw
  have hScard :=
    WilliamsonShmoys.maximal_planar_edge_count_via_euler S hV hSdraw hSmax
  have hRneS : R ≠ S := by
    intro hEq
    subst S
    omega
  exact ⟨S, lt_of_le_of_ne hRS hRneS, hSdraw⟩