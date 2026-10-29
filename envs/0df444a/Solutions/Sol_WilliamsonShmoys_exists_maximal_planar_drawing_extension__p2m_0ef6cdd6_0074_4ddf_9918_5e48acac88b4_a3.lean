-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_extension__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:34:37.553993+00:00
-- url     : https://prove2.me/submissions/ec531847-cdd5-44f3-8b72-2d9dd9e9efbb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let S := {H : SimpleGraph V // G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}
  letI : Fintype S := Fintype.ofFinite S
  have hs : (Finset.univ : Finset S).Nonempty := by
    exact ⟨⟨G, le_rfl, hG⟩, Finset.mem_univ _⟩
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset S)
      (fun X => X.val.edgeSet.ncard) hs
  refine ⟨H.val, H.property.1, ?_, H.property.2, ?_⟩
  · exact hHmax ⟨G, le_rfl, hG⟩ (Finset.mem_univ _)
  · intro K hHK hK
    have hKmem : (⟨K, le_trans H.property.1 hHK, hK⟩ : S) ∈ Finset.univ :=
      Finset.mem_univ _
    have hmax : K.edgeSet.ncard ≤ H.val.edgeSet.ncard :=
      hHmax ⟨K, le_trans H.property.1 hHK, hK⟩ hKmem
    have hsub : H.val.edgeSet ⊆ K.edgeSet :=
      SimpleGraph.edgeSet_subset_edgeSet.mpr hHK
    have heq : H.val.edgeSet = K.edgeSet :=
      Set.eq_of_subset_of_ncard_le hsub hmax
    exact (SimpleGraph.edgeSet_inj.mp heq).symm