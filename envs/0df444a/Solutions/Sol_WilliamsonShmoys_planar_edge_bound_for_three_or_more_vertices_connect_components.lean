-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connect_components
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:49:08.734165+00:00
-- url     : https://prove2.me/submissions/99a68db1-7e66-45bb-b696-79c09ffd9d1d

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, L ≤ T ∧ T.Connected ∧ HasPlanarDrawingOn T :=
  WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1 L hL hCard