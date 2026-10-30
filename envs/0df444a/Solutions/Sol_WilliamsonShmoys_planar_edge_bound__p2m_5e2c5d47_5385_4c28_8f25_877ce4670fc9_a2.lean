-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:28.444298+00:00
-- url     : https://prove2.me/submissions/b2b80153-a848-43d1-aa7a-3dc74c3cfcfa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨K, hHK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1 H hH hcard
  letI : DecidableRel K.Adj := Classical.decRel _
  have hKcount := WilliamsonShmoys.maximal_planar_edge_count__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1 K hKplanar hKmax hcard
  have hmono : H.edgeFinset.card ≤ K.edgeFinset.card := by
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)
  omega