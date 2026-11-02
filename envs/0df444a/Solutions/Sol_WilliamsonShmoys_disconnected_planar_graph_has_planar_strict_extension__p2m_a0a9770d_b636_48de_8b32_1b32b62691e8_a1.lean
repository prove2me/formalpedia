-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_graph_has_planar_strict_extension__p2m_a0a9770d_b636_48de_8b32_1b32b62691e8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:44:59.284692+00:00
-- url     : https://prove2.me/submissions/a74c323b-7d6c-4120-9d5b-d93f9f1cf88e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
import Theorems.Thm_WilliamsonShmoys_strict_simplegraph_supergraph_has_new_edge__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hdisc : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      HasPlanarDrawingOn L ∧
      ∃ u v, L.Adj u v ∧ ¬ K.Adj u v := by
  obtain ⟨L, hsub, hL, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1 K hK
  have hconn :=
    WilliamsonShmoys.maximal_planar_graph_connected__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
      L hL hmax
  have hne : L ≠ K := by
    intro heq
    apply hdisc
    rw [← heq]
    exact hconn
  exact ⟨L, hsub, hL,
    WilliamsonShmoys.strict_simplegraph_supergraph_has_new_edge__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
      K L hsub hne⟩
