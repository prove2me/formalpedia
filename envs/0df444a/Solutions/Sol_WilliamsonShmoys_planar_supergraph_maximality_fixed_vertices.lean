-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximality_fixed_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:37:25.865871+00:00
-- url     : https://prove2.me/submissions/7436be01-3137-4844-9418-2b5e7d9eb094

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) := by 
  classical
  obtain ⟨L, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hM
  exact ⟨L, hMH, hmax.1, fun K hK hKp => le_antisymm (hmax.2 hKp hK) hK⟩
