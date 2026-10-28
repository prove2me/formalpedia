-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_extension_for_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:36:46.45546+00:00
-- url     : https://prove2.me/submissions/2987f673-9819-4bb5-8516-d3711a65fb98

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M →
          WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by 
  classical
  obtain ⟨L, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hK
  exact ⟨L, hMH, hmax.1, fun M hM hMp => le_antisymm (hmax.2 hMp hM) hM⟩
