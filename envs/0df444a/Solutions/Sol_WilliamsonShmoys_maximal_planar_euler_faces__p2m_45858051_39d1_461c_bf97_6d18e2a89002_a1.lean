-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_faces__p2m_45858051_39d1_461c_bf97_6d18e2a89002_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:44.547511+00:00
-- url     : https://prove2.me/submissions/c2c618fa-5464-4c69-a37a-6c8016666234

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
import Theorems.Thm_WilliamsonShmoys_connected_graph_edge_lower_bound__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H) :
    exists f : Nat, H.edgeSet.ncard + 2 = Fintype.card V + f := by
  have hconn : H.Connected :=
    WilliamsonShmoys.maximal_planar_drawing_connected__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
      H hplanar hV hmax
  have hbound : Fintype.card V <= H.edgeSet.ncard + 1 :=
    WilliamsonShmoys.connected_graph_edge_lower_bound__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
      H hconn
  refine ⟨H.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega