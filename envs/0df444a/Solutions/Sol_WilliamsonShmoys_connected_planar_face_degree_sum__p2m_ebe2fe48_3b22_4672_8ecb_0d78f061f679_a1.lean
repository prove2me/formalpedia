-- Prove2me | solution 1 for WilliamsonShmoys_connected_planar_face_degree_sum__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:54:47.761168+00:00
-- url     : https://prove2.me/submissions/95f08814-5c59-4f4c-a177-1a85a5f73065

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_count_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
import Theorems.Thm_WilliamsonShmoys_fin_degree_sequence_from_sum_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
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
    ∃ (degrees : Fin f → ℕ),
      (∀ i, 3 ≤ degrees i) ∧
      (∑ i : Fin f, degrees i) = 2 * G.edgeSet.ncard := by
  have hBounds :=
    WilliamsonShmoys_connected_planar_face_count_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
      G hG hConnected hCard f hEuler
  exact WilliamsonShmoys_fin_degree_sequence_from_sum_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
    f G.edgeSet.ncard hBounds.1 hBounds.2