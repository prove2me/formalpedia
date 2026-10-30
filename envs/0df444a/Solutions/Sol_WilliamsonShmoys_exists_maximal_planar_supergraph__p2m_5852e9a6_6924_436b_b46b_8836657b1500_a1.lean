-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5852e9a6_6924_436b_b46b_8836657b1500_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:43:06.849656+00:00
-- url     : https://prove2.me/submissions/f8ff249a-4fa9-4662-b195-53a40e2b9139

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

/-- A finite planar graph has a maximal planar supergraph on the same vertex set. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let P : Set (SimpleGraph V) :=
    {H | G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}
  have hPfin : P.Finite := Set.toFinite P
  have hPne : P.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨H, hHmax⟩ := hPfin.exists_maximal hPne
  have hHP : H ∈ P := hHmax.1
  refine ⟨H, hHP.1, hHP.2, ?_⟩
  intro K hHK hK
  have hKP : K ∈ P := ⟨hHP.1.trans hHK, hK⟩
  exact le_antisymm (hHmax.2 hKP hHK) hHK
