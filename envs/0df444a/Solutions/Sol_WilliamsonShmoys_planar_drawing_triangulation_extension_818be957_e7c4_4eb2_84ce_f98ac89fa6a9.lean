-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_818be957_e7c4_4eb2_84ce_f98ac89fa6a9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:09:41.411048+00:00
-- url     : https://prove2.me/submissions/5e79fced-85c5-4b94-8559-51d049358deb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨P, hGP, hP, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_extension G hG
  have hcount :=
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing P hV hP hmax
  exact ⟨P, hGP, hP, hcount⟩