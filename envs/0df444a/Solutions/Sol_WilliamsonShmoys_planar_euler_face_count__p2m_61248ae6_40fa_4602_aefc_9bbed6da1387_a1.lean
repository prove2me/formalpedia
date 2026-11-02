-- Prove2me | solution 1 for WilliamsonShmoys.planar_euler_face_count__p2m_61248ae6_40fa_4602_aefc_9bbed6da1387_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:08:01.550457+00:00
-- url     : https://prove2.me/submissions/c207bf29-2974-44f7-9d6c-e790d76f6079
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bounds__p2m_13cac36b_d337_49ef_981f_d43d139f211c_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * K.edgeFinset.card := by
  obtain ⟨hconn_edges, hplanar_edges⟩ :=
    WilliamsonShmoys.connected_planar_edge_bounds__p2m_13cac36b_d337_49ef_981f_d43d139f211c_a2
      K hV hconn hK
  refine ⟨K.edgeFinset.card + 2 - Fintype.card V, ?_, ?_⟩ <;> omega