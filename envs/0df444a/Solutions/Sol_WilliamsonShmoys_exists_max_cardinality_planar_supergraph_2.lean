-- Prove2me | solution 2 for WilliamsonShmoys.exists_max_cardinality_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:08:51.811979+00:00
-- url     : https://prove2.me/submissions/d6be8600-582c-4dc6-b065-6929807bb302

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, N ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  have hfin : ({J : SimpleGraph V | N ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨K, hK, hmax⟩ := Set.exists_max_image _ (fun J : SimpleGraph V => J.edgeSet.ncard) hfin
    ⟨N, le_rfl, hN⟩
  exact ⟨K, hK.1, hK.2, fun L hL hPL => hmax L ⟨hL, hPL⟩⟩
