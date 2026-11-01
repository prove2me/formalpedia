-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_maximizer__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:54.699971+00:00
-- url     : https://prove2.me/submissions/bae5c7f2-bd1f-4238-9866-14ef3691f4d6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
          K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun K => G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have admissible_nonempty : admissible.Nonempty := by
    refine ⟨G, ?_⟩
    simp [admissible, hG]
  obtain ⟨H, hH_mem, hH_max⟩ :=
    Finset.exists_max_image admissible (fun K => K.edgeSet.ncard) admissible_nonempty
  have hH_props := (Finset.mem_filter.mp hH_mem).2
  refine ⟨H, hH_props.1, hH_props.2, ?_⟩
  intro K hHK hK_planar
  have hGK : G ≤ K := le_trans hH_props.1 hHK
  apply hH_max K
  simp [admissible, hGK, hK_planar]