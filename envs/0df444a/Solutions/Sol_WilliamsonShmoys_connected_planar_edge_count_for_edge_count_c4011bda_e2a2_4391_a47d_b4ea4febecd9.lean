-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:49:33.201995+00:00
-- url     : https://prove2.me/submissions/97629f27-122b-470b-b9b4-65a51500e137

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_degree_sum__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler⟩ := WilliamsonShmoys_connected_planar_euler_face_count__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1 G hG hConnected
  obtain ⟨degrees, hDegree, hSum⟩ :=
    WilliamsonShmoys_connected_planar_face_degree_sum__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1 G hG hConnected hCard f hEuler
  have hLower : 3 * f ≤ ∑ i : Fin f, degrees i := by
    calc
      3 * f = f * 3 := Nat.mul_comm 3 f
      _ = ∑ _i : Fin f, 3 := by simp
      _ ≤ ∑ i : Fin f, degrees i :=
        Finset.sum_le_sum (fun i _ => hDegree i)
  rw [hSum] at hLower
  omega