-- Prove2me | solution 2 for WilliamsonShmoys.planar_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:37:22.693998+00:00
-- url     : https://prove2.me/submissions/843b19e9-b097-4fea-ac70-49888c995ac3

import Theorems.Thm_WilliamsonShmoys_has_euler_face_count_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f <= 2 * H.edgeSet.ncard :=
  WilliamsonShmoys.has_euler_face_count_bound H hplanar hconnected hV
