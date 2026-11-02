-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T19:04:01.761132+00:00
-- url     : https://prove2.me/submissions/f8349ae4-4736-425a-8ea3-52f1fdca5cb0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ (J : SimpleGraph V), H ≤ J →
          WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hS : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨H, hH, hmax⟩ := hS.exists_maximal hSne
  refine ⟨H, inferInstance, hH.1, hH.2, ?_⟩
  intro J hHJ hJ
  have hJS : J ∈ S := ⟨hH.1.trans hHJ, hJ⟩
  change ∀ G, G ∈ S → H ≤ G → G ≤ H at hmax
  exact hmax J hJS hHJ
