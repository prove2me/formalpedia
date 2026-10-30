-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:56:18.921845+00:00
-- url     : https://prove2.me/submissions/0efb004a-e813-4806-a134-82e896b3a329

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let S : Set (SimpleGraph V) := {K | G ≤ K ∧ HasPlanarDrawingOn K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨H, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  have hHmem : S H := hHmax.1
  rcases hHmem with ⟨hGH, hHplanar⟩
  refine ⟨H, hGH, hHplanar, ?_, ?_⟩
  · intro K hHK hKplanar
    have hKmem : S K := ⟨hGH.trans hHK, hKplanar⟩
    exact (hHmax.eq_of_le hKmem hHK).symm
  · exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH)