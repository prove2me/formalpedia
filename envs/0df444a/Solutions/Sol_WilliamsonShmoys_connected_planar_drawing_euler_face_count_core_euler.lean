-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_face_count_core_euler
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:16:04.347678+00:00
-- url     : https://prove2.me/submissions/ae200739-8a00-4aa8-b04d-10bdf4082331

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_card_le_edge_ncard_add_one

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by
  have hbound : Fintype.card V ≤ L.edgeSet.ncard + 1 :=
    WilliamsonShmoys.connected_card_le_edge_ncard_add_one L hconn
  refine ⟨L.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega