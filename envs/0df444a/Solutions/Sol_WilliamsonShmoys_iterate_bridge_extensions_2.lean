-- Prove2me | solution 2 for WilliamsonShmoys.iterate_bridge_extensions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:32:05.265918+00:00
-- url     : https://prove2.me/submissions/c0745e88-026f-4bb8-a163-32ae7fdd3db4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (bridge_extension : ∀ (J : SimpleGraph V),
      WilliamsonShmoys.HasPlanarDrawingOn J →
      ¬ (∀ u v : V, Nonempty (J.Walk u v)) →
      ∃ L : SimpleGraph V,
        J ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∃ u v : V, ¬ Nonempty (J.Walk u v) ∧ L.Adj u v) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by 
  classical
  obtain ⟨H, hKH, hmax⟩ := Finite.exists_le_maximal
    (p := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K) hK
  refine ⟨H, hKH, ?_, hmax.1⟩
  by_contra hc
  obtain ⟨L, hHL, hPL, u, v, huv, hL⟩ := bridge_extension H hmax.1 hc
  exact huv ⟨(hmax.2 hPL hHL hL).toWalk⟩
