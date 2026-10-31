-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_726fe57b_9b66_48eb_a490_e0e9926cc417_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:57.70471+00:00
-- url     : https://prove2.me/submissions/9bc6b3f9-58be-422f-97f3-420eb05df80d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_to_edge_maximal__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1
set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Y, hXY, hY, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_extension_to_edge_maximal__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1
      X hX hV
  exact ⟨Y, hXY, hY,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1
      Y hY hV hMax⟩