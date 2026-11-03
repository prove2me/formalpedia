-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:04:48.011142+00:00
-- url     : https://prove2.me/submissions/b3b6eb49-dddb-475a-ab47-587dd978c41d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K ∧
        H.edgeFinset.card ≤ K.edgeSet.ncard := by
  classical
  obtain ⟨K, hHK, hconn, hplan⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a2 H hH hcard
  refine ⟨K, hHK, hconn, hplan, ?_⟩
  have hsub : H.edgeFinset ⊆ K.edgeFinset := SimpleGraph.edgeFinset_mono hHK
  have hcardK : K.edgeFinset.card = K.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  rw [← hcardK]
  exact Finset.card_le_card hsub