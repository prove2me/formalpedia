-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_triangulation_target
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:34:44.396561+00:00
-- url     : https://prove2.me/submissions/887a4f67-3a4b-4c9d-a399-88f25230e45e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) := by 
  classical
  obtain ⟨H, hGH, hmax⟩ := Finite.exists_le_maximal
    (p := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K) hG
  exact ⟨H, hGH, hmax.1, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _),
    fun K h hK => hmax.2 hK h⟩
