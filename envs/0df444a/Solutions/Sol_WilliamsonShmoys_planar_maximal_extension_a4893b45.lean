-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension_a4893b45
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:24:39.171+00:00
-- url     : https://prove2.me/submissions/0207db33-414d-44ef-a8bf-93ac23fc940d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by 
  classical
  obtain ⟨K, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hH
  exact ⟨K, hMH, hmax.1, fun L hK hKp => le_antisymm (hmax.2 hKp hK) hK⟩
