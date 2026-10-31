-- Prove2me | solution 1 for WilliamsonShmoys.connected_maximal_planar_edge_bound__p2m_8955ab15_7b83_4a31_a256_432a7dfdfb1c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:16.41521+00:00
-- url     : https://prove2.me/submissions/5f87b574-b1a9-4c1d-98a9-358e3fe5f2b5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulated_extension_of_planar_drawing__p2m_feadab3c_5ccb_4a82_9ee7_4f0db9bfa441_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hUmax : ∀ W : SimpleGraph V, U ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W = U)
    (hconn : U.Connected) :
    3 * Fintype.card V - 6 ≤ U.edgeSet.ncard := by
  obtain ⟨T, hUT, hTdraw, hTcard⟩ :=
    WilliamsonShmoys.triangulated_extension_of_planar_drawing__p2m_feadab3c_5ccb_4a82_9ee7_4f0db9bfa441_a1
      U hV hU hconn
  have hTU : T = U := hUmax T hUT hTdraw
  subst T
  exact le_of_eq hTcard.symm