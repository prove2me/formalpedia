-- Prove2me | solution 1 for WilliamsonShmoys_connected_planar_face_count_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:30:10.640842+00:00
-- url     : https://prove2.me/submissions/bcf2f9d9-320e-4856-b1d1-4446ebac9027

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_edge_lower_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hCard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : f + Fintype.card V = G.edgeSet.ncard + 2) :
    0 < f ∧ 3 * f ≤ 2 * G.edgeSet.ncard := by
  have hLower := WilliamsonShmoys_connected_edge_lower_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2 G hConnected
  have hUpper := WilliamsonShmoys_planar_edge_upper_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2 G hG hCard
  omega