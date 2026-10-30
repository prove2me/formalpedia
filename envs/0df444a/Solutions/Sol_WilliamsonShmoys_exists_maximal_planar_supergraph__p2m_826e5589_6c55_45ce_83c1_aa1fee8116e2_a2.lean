-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:28:43.195558+00:00
-- url     : https://prove2.me/submissions/c6dd8a8f-b593-4b71-81ec-1f7a3c101a58

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ G.edgeSet ⊆ H.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by
  classical
  let S : Set (SimpleGraph V) :=
    {H | G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}
  have hS_nonempty : S.Nonempty := by
    exact ⟨G, le_rfl, hG⟩
  have hS_finite : S.Finite := Set.toFinite S
  obtain ⟨H, hHmax⟩ := hS_finite.exists_maximal hS_nonempty
  rcases hHmax with ⟨hHmem, hHmax⟩
  rcases hHmem with ⟨hGH, hHplanar⟩
  refine ⟨H, hGH, (SimpleGraph.edgeSet_subset_edgeSet).2 hGH, hHplanar, ?_⟩
  intro K hHK hKplanar
  have hKmem : K ∈ S := ⟨le_trans hGH hHK, hKplanar⟩
  have hKH : K ≤ H := hHmax hKmem hHK
  exact le_antisymm hKH hHK