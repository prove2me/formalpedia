-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:22:56.318112+00:00
-- url     : https://prove2.me/submissions/2f0309c8-3926-4d64-a5d1-78affde370d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_extension_by_joining_components__p2m_10785777_128a_4e88_8513_e417451ea141_a2
import Theorems.Thm_WilliamsonShmoys_finite_graph_extension_maximality__p2m_8122a02e_177a_44bd_9de8_e1e79416f7a3_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (M : SimpleGraph V), ∃ (dM : DecidableRel M.Adj),
      (letI : DecidableRel M.Adj := dM
       HasPlanarDrawingOn M ∧
       N.edgeFinset.card ≤ M.edgeFinset.card ∧
       M.Connected) := by
  classical
  let P : SimpleGraph V → Prop := HasPlanarDrawingOn
  have hstep : ∀ K : SimpleGraph V, N ≤ K → P K → ¬ K.Connected →
      ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧ K ≠ L := by
    intro K _ hK hdis
    obtain ⟨u, v, hsep, L, hKL, hEdge, hL, hne⟩ :=
      WilliamsonShmoys.drawable_extension_by_joining_components__p2m_10785777_128a_4e88_8513_e417451ea141_a2
        K hK hcard hdis
    exact ⟨L, hKL, hL, hne.symm⟩
  obtain ⟨M, hNM, hM, hconn⟩ :=
    WilliamsonShmoys.finite_graph_extension_maximality__p2m_8122a02e_177a_44bd_9de8_e1e79416f7a3_a2
      N P hN hstep
  letI : DecidableRel M.Adj := Classical.decRel _
  refine ⟨M, Classical.decRel _, ?_⟩
  refine ⟨hM, ?_, hconn⟩
  apply Finset.card_le_card
  exact SimpleGraph.edgeFinset_mono hNM