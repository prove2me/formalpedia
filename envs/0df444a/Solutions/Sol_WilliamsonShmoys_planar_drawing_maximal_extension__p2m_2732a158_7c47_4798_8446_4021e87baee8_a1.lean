-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2732a158_7c47_4798_8446_4021e87baee8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:01:08.058439+00:00
-- url     : https://prove2.me/submissions/8147ec0d-5da8-4180-984e-8d01c8c9b46e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite_maximal__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_drawing_mono__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hHplanar : HasPlanarDrawingOn H) :
    ∃ T : SimpleGraph V, H ≤ T ∧ H.edgeSet ⊆ T.edgeSet ∧
      HasPlanarDrawingOn T ∧
      (∀ S : SimpleGraph V, T ≤ S → HasPlanarDrawingOn S → S = T) := by
  let P : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hP : ∃ G, P G := ⟨H, le_rfl, hHplanar⟩
  obtain ⟨T, hTP, hTmax⟩ := WilliamsonShmoys.planar_drawing_maximal_extension_finite_maximal__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1 P hP
  have hHT : H ≤ T := hTP.1
  have hTplanar : HasPlanarDrawingOn T := hTP.2
  refine ⟨T, hHT, SimpleGraph.edgeSet_mono hHT, hTplanar, ?_⟩
  intro S hTS hSplanar
  apply hTmax S hTS
  exact ⟨le_trans hHT hTS, hSplanar⟩