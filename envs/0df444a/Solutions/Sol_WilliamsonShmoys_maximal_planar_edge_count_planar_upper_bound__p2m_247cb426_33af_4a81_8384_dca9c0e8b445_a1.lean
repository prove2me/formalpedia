-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_planar_upper_bound__p2m_247cb426_33af_4a81_8384_dca9c0e8b445_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:10.273988+00:00
-- url     : https://prove2.me/submissions/7a549998-388c-44c3-a8f0-ed975bf7e679
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_set__p2m_73aab3ca_7b81_4c01_b6b0_263310be94b1_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨F, hsub, hF⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_edge_set__p2m_73aab3ca_7b81_4c01_b6b0_263310be94b1_a1
      G hG hcard
  calc
    G.edgeFinset.card ≤ F.card := Finset.card_le_card hsub
    _ = 3 * Fintype.card V - 6 := hF