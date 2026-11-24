-- Prove2me | solution 1 for WilliamsonShmoys.euler_characteristic_of_planar_drawing__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:15:26.721029+00:00
-- url     : https://prove2.me/submissions/6b9ba60d-61cb-431e-bc15-4eba960ae17d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_for_face_accounting_57972424
import Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound_from_embedding
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_face_accounting_57972424
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_b3c9bfa4_c900_4902_b62c_e651fcb234b7_a1
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_large__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a4
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_54a0e51c

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hConn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : Exists fun F : Nat => Fintype.card V + F = G.edgeSet.ncard + 2 := by
  exact planar_drawing_euler_for_face_accounting_57972424 G hG hConn
