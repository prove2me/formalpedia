-- Prove2me | solution 3 for WilliamsonShmoys.iterate_bridge_extensions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:32:18.653088+00:00
-- url     : https://prove2.me/submissions/c9592abc-94ca-494c-b672-88873c6938fc

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
  have hfin : ({J : SimpleGraph V | K ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨H, hH⟩ := hfin.exists_maximal ⟨K, le_rfl, hK⟩
  refine ⟨H, hH.prop.1, ?_, hH.prop.2⟩
  by_contra hc
  obtain ⟨L, hL, hPL, u, v, huv, hadj⟩ := bridge_extension H hH.prop.2 hc
  have hLH : L ≤ H := hH.2 ⟨le_trans hH.prop.1 hL, hPL⟩ hL
  exact huv ⟨SimpleGraph.Walk.cons (hLH hadj) SimpleGraph.Walk.nil⟩
