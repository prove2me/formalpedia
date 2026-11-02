-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:40:34.22051+00:00
-- url     : https://prove2.me/submissions/0489a8ae-4477-4d4e-aa76-f31a62f598f7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : Nat.le 3 (Fintype.card V)) :
    Nat.le (H.edgeFinset.card + 6) (3 * Fintype.card V) := by
  letI : DecidableRel H.Adj := dH
  have hNcardPlus :
      H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc H hn hH
  have hNcard :
      H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
    omega
  have hFinset :
      H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
    simpa using
      (WilliamsonShmoys.edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1
        H dH hNcard)
  have hSix : 6 ≤ 3 * Fintype.card V := by
    omega
  calc
    H.edgeFinset.card + 6 ≤ (3 * Fintype.card V - 6) + 6 :=
      Nat.add_le_add_right hFinset 6
    _ = 3 * Fintype.card V := Nat.sub_add_cancel hSix
