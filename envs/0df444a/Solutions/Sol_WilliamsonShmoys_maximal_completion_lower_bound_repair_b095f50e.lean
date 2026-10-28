-- Prove2me | solution 1 for WilliamsonShmoys.maximal_completion_lower_bound_repair_b095f50e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:57:26.487355+00:00
-- url     : https://prove2.me/submissions/d16622bf-44b0-405f-8147-66bf6fb2455a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_repair_b095f50e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ U : SimpleGraph V,
      W ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ W) :
    3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by
  obtain ⟨U, hWU, hUplanar, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_repair_b095f50e W hV hW
  have hUW : U ≤ W := hmax U hWU hUplanar
  have hEq : U = W := le_antisymm hUW hWU
  rw [hEq] at hcount
  omega