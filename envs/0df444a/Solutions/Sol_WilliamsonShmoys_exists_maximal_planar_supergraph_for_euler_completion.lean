-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_euler_completion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:53:17.400252+00:00
-- url     : https://prove2.me/submissions/31a64c7f-b87b-41c9-b669-4628c4d40012

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      N <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      (forall L : SimpleGraph V,
        K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) := by
  classical
  have hfin : ({J : SimpleGraph V | N ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨K, hK⟩ := hfin.exists_maximal ⟨N, le_rfl, hN⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun L hL hPL => hK.2 ⟨le_trans hK.prop.1 hL, hPL⟩ hL⟩
