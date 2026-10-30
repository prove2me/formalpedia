-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_of_maximal__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:10.822934+00:00
-- url     : https://prove2.me/submissions/443c3a73-aeef-47a4-85f2-dd893d91002e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_connected__p2m_8955ab15_7b83_4a31_a256_432a7dfdfb1c_a1
import Theorems.Thm_WilliamsonShmoys_connected_maximal_planar_edge_bound__p2m_8955ab15_7b83_4a31_a256_432a7dfdfb1c_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hUmax : ∀ W : SimpleGraph V, U ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W = U) :
    3 * Fintype.card V - 6 ≤ U.edgeSet.ncard := by
  have hconn :=
    WilliamsonShmoys.maximal_planar_connected__p2m_8955ab15_7b83_4a31_a256_432a7dfdfb1c_a1
      U hV hU hUmax
  exact WilliamsonShmoys.connected_maximal_planar_edge_bound__p2m_8955ab15_7b83_4a31_a256_432a7dfdfb1c_a1
    U hV hU hUmax hconn
