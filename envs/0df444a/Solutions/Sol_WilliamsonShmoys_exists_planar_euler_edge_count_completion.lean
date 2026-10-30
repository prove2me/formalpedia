-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_euler_edge_count_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:14:19.742544+00:00
-- url     : https://prove2.me/submissions/9fffa80c-eeb6-449f-afe6-9d1a1a2706a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_euler_edge_count_completion_maximal_extension_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
import Theorems.Thm_WilliamsonShmoys_maximal_planar_has_euler_edge_count_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hHJ, hJ, hmax⟩ :=
    WilliamsonShmoys.exists_planar_euler_edge_count_completion_maximal_extension_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
      H hH
  exact ⟨J, hHJ, hJ,
    WilliamsonShmoys.maximal_planar_has_euler_edge_count_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
      J hV hJ hmax⟩
