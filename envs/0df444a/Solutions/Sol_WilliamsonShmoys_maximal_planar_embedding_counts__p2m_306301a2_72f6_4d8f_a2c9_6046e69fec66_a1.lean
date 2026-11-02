-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_embedding_counts__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:52:25.261093+00:00
-- url     : https://prove2.me/submissions/9aa90d5f-cb57-41f1-9158-935ed9630069
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    letI : (G : SimpleGraph V) → DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ F : ℕ,
      (Fintype.card V : ℤ) - (L.edgeFinset.card : ℤ) + (F : ℤ) = 2 ∧
      3 * F = 2 * L.edgeFinset.card := by
  letI : (G : SimpleGraph V) → DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  have hupper : L.edgeFinset.card ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_count_upper__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
      L hcard hL
  have hlower : 3 * Fintype.card V - 6 ≤ L.edgeFinset.card :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
      L hcard hconn hL hmax
  have he : L.edgeFinset.card = 3 * Fintype.card V - 6 := Nat.le_antisymm hupper hlower
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega