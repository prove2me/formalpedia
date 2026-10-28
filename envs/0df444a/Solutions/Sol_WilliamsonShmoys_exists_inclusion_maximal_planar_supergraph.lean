-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:44:03.324563+00:00
-- url     : https://prove2.me/submissions/0b4a42ea-30fc-4dc9-a83d-f1113f0c6693

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  have hfin : ({J : SimpleGraph V | H ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨K, hK⟩ := hfin.exists_maximal ⟨H, le_rfl, hH⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun L hL hPL => hK.2 ⟨le_trans hK.prop.1 hL, hPL⟩ hL⟩
