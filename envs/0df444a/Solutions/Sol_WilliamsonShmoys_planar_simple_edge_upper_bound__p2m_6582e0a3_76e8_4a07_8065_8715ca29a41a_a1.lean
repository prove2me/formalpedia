-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_upper_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:56:30.036954+00:00
-- url     : https://prove2.me/submissions/b449a31a-1d0b-4f72-a109-571af9919f6f

import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_2120accc_e77c_4707_8c72_d7b3ece39068_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨H, hNH, hHplanar, hHcard⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_2120accc_e77c_4707_8c72_d7b3ece39068_a1
      N hN hcard
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hle : N.edgeFinset.card ≤ H.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hNH)
  omega