-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:40:26.918443+00:00
-- url     : https://prove2.me/submissions/9fb98889-0365-4811-914f-d391dba57a91

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hbound : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6) :
    (letI : DecidableRel K.Adj := dK;
     K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel K.Adj := dK
  have hcard : Fintype.card K.edgeSet ≤ 3 * Fintype.card V - 6 := by
    rw [Set.fintypeCard_eq_ncard]
    exact hbound
  calc
    K.edgeFinset.card = Fintype.card K.edgeSet := K.edgeFinset_card
    _ ≤ 3 * Fintype.card V - 6 := hcard