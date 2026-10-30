-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b707ad4a_77a6_470e_9bb1_a016cbfcb978_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:19:54.485005+00:00
-- url     : https://prove2.me/submissions/294239d1-9b0c-4393-b656-8b0449b74586
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension__p2m_f0b6b169_74af_4776_af38_cf20fc29acd0_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
      HasPlanarDrawingOn L → L.edgeSet = K.edgeSet)
    (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_extension__p2m_f0b6b169_74af_4776_af38_cf20fc29acd0_a1
      K hK hV
  rw [hmax L hKL hL] at hcount
  exact hcount