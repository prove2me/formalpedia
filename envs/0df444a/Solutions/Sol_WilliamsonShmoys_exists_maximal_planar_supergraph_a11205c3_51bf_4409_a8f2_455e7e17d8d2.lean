-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_a11205c3_51bf_4409_a8f2_455e7e17d8d2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:36:32.87672+00:00
-- url     : https://prove2.me/submissions/5de1a9e6-5497-4dd5-b641-a2908927810a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        (∀ ⦃u v : V⦄, L.Adj u v → K.Adj u v) := by 
  classical
  obtain ⟨K, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hG
  exact ⟨K, fun u v h => hMH h, hmax.1, fun L hK hKp => hmax.2 hKp (fun u v h => hK h)⟩
