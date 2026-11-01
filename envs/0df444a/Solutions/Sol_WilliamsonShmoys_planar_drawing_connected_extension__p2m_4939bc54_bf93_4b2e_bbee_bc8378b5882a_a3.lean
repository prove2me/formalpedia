-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:29:15.144979+00:00
-- url     : https://prove2.me/submissions/fb83c403-2b1b-48ef-a55a-f4a6dec91118
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a1
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
    WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a1 H hH
  refine ⟨K, hHK, hconn, hplan, ?_⟩
  have hsub : H.edgeFinset ⊆ K.edgeFinset := SimpleGraph.edgeFinset_mono hHK
  have hcardK : K.edgeFinset.card = K.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  rw [← hcardK]
  exact Finset.card_le_card hsub