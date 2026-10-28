-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_finite_maximal_supergraph_cffe1994_9450_4d5a_8cf0_7263df183181
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:12:53.746431+00:00
-- url     : https://prove2.me/submissions/7842148e-fcee-4e39-97d2-2cdc4cc2f054

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun M : SimpleGraph V =>
      G <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (forall N : SimpleGraph V,
        M <= N ->
        WilliamsonShmoys.HasPlanarDrawingOn N ->
        N = M) := by 
  classical
  obtain ⟨H, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hG
  exact ⟨H, hMH, hmax.1, fun K hK hKp => le_antisymm (hmax.2 hKp hK) hK⟩
