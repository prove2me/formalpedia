-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_maximal_extension__p2m_7ae41427_8c04_422e_92b9_bd045ddeec30_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:46:54.476267+00:00
-- url     : https://prove2.me/submissions/5ab6430e-ed06-4f16-b41f-2e6f4a7a2e17

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      L ≤ H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) := by
  classical
  let S : Set (SimpleGraph V) := {K | L ≤ K ∧ HasPlanarDrawingOn K}
  have hSfinite : S.Finite := Set.toFinite S
  have hLmem : L ∈ S := by
    simp [S, hL]
  obtain ⟨H, hLH, hHmax⟩ := hSfinite.exists_le_maximal hLmem
  have hHmem : H ∈ S := hHmax.1
  refine ⟨H, hHmem.2, hLH, ?_, ?_⟩
  · exact Set.ncard_mono (SimpleGraph.edgeSet_mono hLH)
  · intro K hHK hK
    exact hHmax.2 ⟨hLH.trans hHK, hK⟩ hHK