-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists_fixed_vertex_set
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:48:30.589556+00:00
-- url     : https://prove2.me/submissions/ff72c947-5465-403b-9ce3-4affe5c46d16

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ H : SimpleGraph V,
        M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ M := by
  classical
  have hfin : ({J : SimpleGraph V | L ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨M, hM⟩ := hfin.exists_maximal ⟨L, le_rfl, hL⟩
  exact ⟨M, hM.prop.1, hM.prop.2, fun H hH hPH => hM.2 ⟨le_trans hM.prop.1 hH, hPH⟩ hH⟩
