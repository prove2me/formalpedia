-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_extension_max_card__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:03:42.714062+00:00
-- url     : https://prove2.me/submissions/2be27922-0323-476d-9756-9d36e1984c2a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
        ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
          K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hSfinite : S.Finite :=
    Set.finite_univ.subset (by
      intro K hK
      exact Set.mem_univ K)
  have hSne : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨H, hH, hmax⟩ :=
    Set.exists_max_image S (fun K => K.edgeSet.ncard) hSfinite hSne
  refine ⟨H, hH.1, hH.2, ?_, ?_⟩
  · exact hmax G ⟨le_rfl, hG⟩
  · intro K hGK hK
    exact hmax K ⟨hGK, hK⟩