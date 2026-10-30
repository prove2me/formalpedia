-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_9f95e338
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:37:09.226496+00:00
-- url     : https://prove2.me/submissions/0fe77126-5971-476a-9a0e-e127ecf2c38d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hUdraw, hUbound⟩ :=
    WilliamsonShmoys.drawable_supergraph_edge_bound (V := V) T hdraw hV
  have hUT : U ≤ T := hmax U hTU hUdraw
  have hEq : U = T := le_antisymm hUT hTU
  rw [← hEq]
  exact hUbound