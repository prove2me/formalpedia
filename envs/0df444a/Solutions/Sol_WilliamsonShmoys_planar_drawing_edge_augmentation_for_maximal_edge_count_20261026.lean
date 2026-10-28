-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_augmentation_for_maximal_edge_count_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:02:16.365964+00:00
-- url     : https://prove2.me/submissions/5d8f51d4-edbb-4800-8ef8-146679cbce04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_818be957_e7c4_4eb2_84ce_f98ac89fa6a9

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hsmall : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ P ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn P := by
  obtain ⟨P, hGP, hdraw, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_818be957_e7c4_4eb2_84ce_f98ac89fa6a9
      G hV hG
  refine ⟨P, hGP, ?_, hdraw⟩
  intro hEq
  have hGcard : G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hEq] using hcard
  omega
