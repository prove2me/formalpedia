-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:38:14.754039+00:00
-- url     : https://prove2.me/submissions/c79b616b-7758-44e0-82ad-337cc46c5696

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have h₁ := WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1 M hM hCard
  have h₂ := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1 M hM hCard hMax
  omega