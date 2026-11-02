-- Prove2me | solution 1 for WilliamsonShmoys_planar_drawing_maximal_extension__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:42:48.316334+00:00
-- url     : https://prove2.me/submissions/d3ac9cfd-d82d-4453-8cc1-8ae27a029839

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
      ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨H, le_rfl, hH⟩
  obtain ⟨G, hG, hGmax⟩ := hSfin.exists_maximal hSne
  refine ⟨G, hG.1, hG.2, ?_⟩
  intro K hGK hK
  have hKS : K ∈ S := ⟨le_trans hG.1 hGK, hK⟩
  have hKG : K ≤ G := hGmax hKS hGK
  exact (le_antisymm hGK hKG).symm