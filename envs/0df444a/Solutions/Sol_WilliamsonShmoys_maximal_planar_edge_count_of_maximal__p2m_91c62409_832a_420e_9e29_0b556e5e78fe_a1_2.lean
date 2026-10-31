-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_of_maximal__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:40:42.563079+00:00
-- url     : https://prove2.me/submissions/423017cb-138d-4cb6-968d-4598a5159ee0

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_47cfe247_f32d_4afb_b363_54161b3a97c2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hU : WilliamsonShmoys.HasPlanarDrawingOn U) (hUmax : ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U) : 3 * Fintype.card V - 6 ≤ U.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_bound_47cfe247_f32d_4afb_b363_54161b3a97c2 U hV hU hUmax
