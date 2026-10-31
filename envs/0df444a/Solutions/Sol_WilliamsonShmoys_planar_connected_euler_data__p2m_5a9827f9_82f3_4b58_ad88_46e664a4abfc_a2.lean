-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_euler_data__p2m_5a9827f9_82f3_4b58_ad88_46e664a4abfc_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:39:19.051252+00:00
-- url     : https://prove2.me/submissions/04e43846-6862-4b0b-b8fa-153b8b15c56b

import Theorems.Thm_WilliamsonShmoys_has_euler_face_count_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hConnected : M.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
        3 * f ≤ 2 * M.edgeSet.ncard :=
  WilliamsonShmoys.has_euler_face_count_bound M hM hConnected hCard
