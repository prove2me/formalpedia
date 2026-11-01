-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_1d9982e7_ae2e_41b5_99c8_f768b7d6d77d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:49:37.887605+00:00
-- url     : https://prove2.me/submissions/b00ef120-a50b-4b3a-81c0-963642100ab8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_card_le_edgeFinset_add_one_of_connected__p2m_de496d36_7d00_43e9_8f8b_fa9ee9576ec1_a3

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ F : ℕ, Fintype.card V + F = K.edgeFinset.card + 2 := by
  have hcard := WilliamsonShmoys.card_le_edgeFinset_add_one_of_connected__p2m_de496d36_7d00_43e9_8f8b_fa9ee9576ec1_a3 K hconn
  refine ⟨K.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega