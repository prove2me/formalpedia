-- Prove2me | solution 1 for WilliamsonShmoys.planar_euler_face_count__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:02:37.78698+00:00
-- url     : https://prove2.me/submissions/e1526e39-1a1c-4754-b2b9-a7b3744c6af1

import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hconn : K.Connected) : Exists fun f : Nat => Fintype.card V + f = K.edgeSet.ncard + 2 :=
  WilliamsonShmoys.connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1 K hK hconn
