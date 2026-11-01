-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_3b70d152_dbfb_4f09_8d03_767be9da3cd3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:14:10.046333+00:00
-- url     : https://prove2.me/submissions/e291dfc0-2e26-45ae-ac7b-cf9a487ae19a

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a9
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a9 H hH hcard
