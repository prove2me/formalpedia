-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_055d45fa_a44d_4012_991d_80fcbbc5becb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:19.930808+00:00
-- url     : https://prove2.me/submissions/43a3da7c-29b4-48a0-9792-77d6fc2e1cc2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  obtain ⟨T, hLT, hTconn, hTplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
      L hL hcard
  have hTbound :=
    WilliamsonShmoys.connected_planar_edge_count_bound__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
      T hTplanar hTconn hcard
  have hsub : L.edgeFinset ⊆ T.edgeFinset := SimpleGraph.edgeFinset_mono hLT
  have hcards : L.edgeFinset.card ≤ T.edgeFinset.card := Finset.card_le_card hsub
  omega
