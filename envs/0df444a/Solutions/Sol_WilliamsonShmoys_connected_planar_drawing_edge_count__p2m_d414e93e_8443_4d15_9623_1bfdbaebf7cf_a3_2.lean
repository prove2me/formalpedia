-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:26:43.218024+00:00
-- url     : https://prove2.me/submissions/b1c4f990-26bb-4a75-81d8-8802bdd6150d

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_face_accounting_57972424

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_face_accounting_57972424 M hM hconn hV
