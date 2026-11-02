-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_extension_ncard__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:42.321045+00:00
-- url     : https://prove2.me/submissions/3d4c3a18-8f2f-45f6-b4f0-4da94e3f1f9b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
          M.edgeSet.ncard ≤ L.edgeSet.ncard := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
  have hKmem : K ∈ S := by
    simp [S, hK]
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeSet.ncard) ⟨K, hKmem⟩
  refine ⟨L, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hLmem).2.1
  · exact (Finset.mem_filter.mp hLmem).2.2
  · intro M hKM hM
    have hMmem : M ∈ S := by
      simp [S, hKM, hM]
    exact hLmax M hMmem