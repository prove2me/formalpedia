-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d133570c_99c6_41e5_a60e_ff6fc0c72c59_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:42.265229+00:00
-- url     : https://prove2.me/submissions/286be84f-deeb-457a-9350-701de9c68e49
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_81030912_3569_483c_b042_44cc0f2e2aea_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := dK;
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel K.Adj := dK
  obtain ⟨H, dH, hsub, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_81030912_3569_483c_b042_44cc0f2e2aea_a1
      K dK hK hcard
  letI : DecidableRel H.Adj := dH
  calc
    K.edgeFinset.card ≤ H.edgeFinset.card := Finset.card_le_card hsub
    _ = 3 * Fintype.card V - 6 := hHcard