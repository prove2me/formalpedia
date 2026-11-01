-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_component_partition__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:09:44.795125+00:00
-- url     : https://prove2.me/submissions/20f8ba4e-7ddc-4ac7-99b1-cd0bdadcb920

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_component_partition__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1
import Theorems.Thm_WilliamsonShmoys_induced_planar_drawing_restrict__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ parts : Finset (Finset V),
      (∀ v, ∃ C, C ∈ parts ∧ v ∈ C) ∧
      (∀ C, C ∈ parts → C.Nonempty) ∧
      (∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D) ∧
      (∀ u v, M.Adj u v → ∃ C, C ∈ parts ∧ u ∈ C ∧ v ∈ C) ∧
      (∀ C, C ∈ parts → (M.induce (C : Set V)).Connected) ∧
      (∀ C, C ∈ parts → WilliamsonShmoys.HasPlanarDrawingOn (M.induce (C : Set V))) := by
  obtain ⟨parts, hcover, hnonempty, hdisjoint, hedge, hconnected⟩ :=
    WilliamsonShmoys.connected_component_partition__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1 M
  refine ⟨parts, hcover, hnonempty, hdisjoint, hedge, hconnected, ?_⟩
  intro C hC
  exact WilliamsonShmoys.induced_planar_drawing_restrict__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1 M hdraw C
