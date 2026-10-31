-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:14:24.963402+00:00
-- url     : https://prove2.me/submissions/d739d788-ee05-4642-8360-ce92fadf95cd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}
  have hSfinite : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨H, hHmax⟩ := hSfinite.exists_maximal hSne
  have hHmem : H ∈ S := hHmax.1
  refine ⟨H, hHmem.1, hHmem.2, ?_⟩
  intro K hHK hK
  have hKmem : K ∈ S := ⟨hHmem.1.trans hHK, hK⟩
  exact le_antisymm (hHmax.2 hKmem hHK) hHK