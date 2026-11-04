-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_certificate__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T21:14:34.829209+00:00
-- url     : https://prove2.me/submissions/06cfac03-9a63-4f74-8153-80d55e27c3e1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_boundary_lengths_at_euler_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (F : Nat) (faceLength : Fin F → Nat),
      Fintype.card V + F = K.edgeFinset.card + 2 ∧
      (∑ i : Fin F, faceLength i) = 2 * K.edgeFinset.card ∧
      ∀ i, 3 ≤ faceLength i := by
  obtain ⟨F, hEulerInt, _⟩ :=
    WilliamsonShmoys.planar_drawing_face_count__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
      K hK hconn hV
  have hEuler : Fintype.card V + F = K.edgeFinset.card + 2 := by
    omega
  obtain ⟨length, hsum, hlength⟩ :=
    WilliamsonShmoys.planar_drawing_boundary_lengths_at_euler_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
      K hK hconn hV F hEuler
  exact ⟨F, length, hEuler, hsum, hlength⟩
