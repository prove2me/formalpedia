-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4d475df2_1a8a_43aa_9ce4_014b937605e8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:43:30.802983+00:00
-- url     : https://prove2.me/submissions/73abca24-3f4d-4305-a0e7-a6f0764f949f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G ≤ H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | WilliamsonShmoys.HasPlanarDrawingOn K ∧ G ≤ K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := by
    refine ⟨G, ?_⟩
    simp [S, hG]
  obtain ⟨H, hHmem, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  have hH : WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H := by
    simpa [S] using hHmem
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  have hKmem : K ∈ S := by
    change WilliamsonShmoys.HasPlanarDrawingOn K ∧ G ≤ K
    exact ⟨hK, hH.2.trans hHK⟩
  exact hHmax hKmem hHK