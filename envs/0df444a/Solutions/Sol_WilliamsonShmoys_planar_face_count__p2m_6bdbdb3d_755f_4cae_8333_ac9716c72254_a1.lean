-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:38:39.280225+00:00
-- url     : https://prove2.me/submissions/12811a26-6811-471a-b1b7-ccf83141172d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected) :
    (letI : DecidableRel K.Adj := Classical.decRel _;
      ∃ f : Nat,
        Fintype.card V + f = K.edgeFinset.card + 2 ∧
        3 * f ≤ 2 * K.edgeFinset.card) := by
  letI : DecidableRel K.Adj := Classical.decRel _
  obtain ⟨f, heuler, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_face_count__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
      K hK hconn hcard
  refine ⟨f, ?_, hbound⟩
  have hi : ((Fintype.card V + f : ℕ) : ℤ) =
      ((K.edgeFinset.card + 2 : ℕ) : ℤ) := by
    push_cast
    omega
  exact_mod_cast hi