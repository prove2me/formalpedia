-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_repair3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:00:24.595229+00:00
-- url     : https://prove2.me/submissions/2e8f8222-cf84-44eb-830f-3f91e3a176bc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_1b39b828_58fc_4ef1_a477_eeaba85e9424
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_1b39b828_58fc_4ef1_a477_eeaba85e9424

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_1b39b828_58fc_4ef1_a477_eeaba85e9424 L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_1b39b828_58fc_4ef1_a477_eeaba85e9424 M hM hCard hmax⟩
