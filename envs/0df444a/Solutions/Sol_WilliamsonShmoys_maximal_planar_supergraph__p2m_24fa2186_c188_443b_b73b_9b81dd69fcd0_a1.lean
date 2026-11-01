-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:30:41.89346+00:00
-- url     : https://prove2.me/submissions/c65a07b7-0210-4d63-b551-e0e34e1f237b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {U : Type} [Fintype U] [LinearOrder U]
    (G : SimpleGraph U) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card U) :
    ∃ H : SimpleGraph U, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph U, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let S : Set (SimpleGraph U) := {K | G ≤ K ∧ HasPlanarDrawingOn K}
  have hS_nonempty : S.Nonempty := ⟨G, le_rfl, hdraw⟩
  have hS_finite : S.Finite := Set.toFinite S
  obtain ⟨H, hH, hmax⟩ := hS_finite.exists_maximal hS_nonempty
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hKdraw
  have hK : K ∈ S := ⟨le_trans hH.1 hHK, hKdraw⟩
  have hKH : K ≤ H := hmax hK hHK
  exact le_antisymm hKH hHK