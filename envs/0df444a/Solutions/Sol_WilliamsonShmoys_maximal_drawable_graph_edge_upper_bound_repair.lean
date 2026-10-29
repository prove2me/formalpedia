-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_upper_bound_repair
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:07:51.465529+00:00
-- url     : https://prove2.me/submissions/c549525a-960f-4684-ba06-637cfe5106ef

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_yields_euler_face_data
import Theorems.Thm_WilliamsonShmoys_euler_face_data_implies_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  classical
  let m : ℕ := L.edgeSet.ncard
  by_cases hm : 2 ≤ m
  · obtain ⟨f, c, heuler, hc, hdegree⟩ :=
      WilliamsonShmoys.planar_drawing_yields_euler_face_data L hV hL hm
    exact WilliamsonShmoys.euler_face_data_implies_edge_bound
      hV hm heuler hc hdegree
  · have hm' : m ≤ 1 := by omega
    omega
