-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_exists_maximal_c67fb017
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:43:02.334391+00:00
-- url     : https://prove2.me/submissions/85dfd408-729c-4a37-ae5a-b48d7753353b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by 
  classical
  obtain ⟨H, hLH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hL
  refine ⟨H, hLH, hmax.1, fun K hK hKp => hmax.2 hKp hK, ?_⟩
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hLH) (Set.toFinite _)
