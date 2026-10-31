-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:39:53.303799+00:00
-- url     : https://prove2.me/submissions/5991c3ef-8f9e-4e9d-a010-3c0625422164

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧ M.edgeSet.ncard ≤ H.edgeSet.ncard ∧
        WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ N : SimpleGraph V, H ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ H := by
  classical
  let s : Set (SimpleGraph V) :=
    {H | M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}
  have hsFinite : s.Finite := Set.toFinite s
  have hsNonempty : s.Nonempty := ⟨M, le_rfl, hDraw⟩
  obtain ⟨H, hHmax⟩ := hsFinite.exists_maximal hsNonempty
  have hHmem : H ∈ s := hHmax.1
  have hHmaximal : ∀ N, N ∈ s → H ≤ N → N ≤ H := hHmax.2
  refine ⟨H, hHmem.1, ?_, hHmem.2, ?_⟩
  · exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hHmem.1)
  · intro N hHN hNDraw
    exact hHmaximal N ⟨hHmem.1.trans hHN, hNDraw⟩ hHN