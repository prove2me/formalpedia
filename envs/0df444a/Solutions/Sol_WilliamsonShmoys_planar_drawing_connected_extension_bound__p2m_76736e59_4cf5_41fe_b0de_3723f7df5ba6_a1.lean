-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:04:56.024844+00:00
-- url     : https://prove2.me/submissions/76af09b7-f182-4fc9-a03e-805e09ebcaba

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_d270c124_96c5_427a_8655_88aa20edeadc_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  obtain ⟨K, hHK, hKC, hDrawK⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_d270c124_96c5_427a_8655_88aa20edeadc_a1
      H hDraw hV
  exact ⟨K, hHK, hKC, hDrawK, Set.ncard_mono (SimpleGraph.edgeSet_mono hHK)⟩