-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_76f2d72e_f140_4cd7_bf10_fd0bb7e9203e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:53:27.810291+00:00
-- url     : https://prove2.me/submissions/cc6aa8fe-8e8b-4d43-ba39-127c33f69e76

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a9
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a9 H hH hcard