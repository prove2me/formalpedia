-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_face_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:21:20.071544+00:00
-- url     : https://prove2.me/submissions/31deedc1-69c4-4a05-a18f-0b0fcf453d27

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_formula
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound_for_face_inequality

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hPconn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = P.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * P.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ := WilliamsonShmoys.connected_planar_euler_formula
    P hPdraw hPconn hCard
  refine ⟨f, hEuler, ?_⟩
  have hEdge := WilliamsonShmoys.connected_planar_edge_count_bound_for_face_inequality
    P hPdraw hPconn hCard
  omega