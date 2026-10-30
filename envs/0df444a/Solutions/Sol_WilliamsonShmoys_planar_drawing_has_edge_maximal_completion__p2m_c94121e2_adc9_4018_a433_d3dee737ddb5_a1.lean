-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_edge_maximal_completion__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:13.702864+00:00
-- url     : https://prove2.me/submissions/9b91cc62-5de3-4436-99f6-0509e74b05d7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1
import Theorems.Thm_finite_graph_property_has_maximal_extension__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        (∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by
  have hmono : ∀ {G F : SimpleGraph V}, G ≤ F →
      WilliamsonShmoys.HasPlanarDrawingOn F →
      WilliamsonShmoys.HasPlanarDrawingOn G := by
    intro G F hGF hF
    exact WilliamsonShmoys.planarDrawingOn_mono__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1 hGF hF
  exact finite_graph_property_has_maximal_extension__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1
    V WilliamsonShmoys.HasPlanarDrawingOn hmono H hplanar