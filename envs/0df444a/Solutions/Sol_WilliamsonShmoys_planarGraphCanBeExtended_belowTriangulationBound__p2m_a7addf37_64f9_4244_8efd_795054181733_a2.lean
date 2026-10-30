-- Prove2me | solution 1 for WilliamsonShmoys.planarGraphCanBeExtended_belowTriangulationBound__p2m_a7addf37_64f9_4244_8efd_795054181733_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:43.737847+00:00
-- url     : https://prove2.me/submissions/5dbfc48f-1f0a-472a-a2e1-8617a46e402b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_maximal_supergraph__p2m_8bebbcb3_63fa_47e0_bd08_43c40080b6a9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8bebbcb3_63fa_47e0_bd08_43c40080b6a9_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hlt : M.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ N : SimpleGraph V, LE.le M N ∧ HasPlanarDrawingOn N ∧ N ≠ M := by
  obtain ⟨N, hMN, hN, hcard, hmax⟩ :=
    WilliamsonShmoys.planarDrawingOn_has_maximal_supergraph__p2m_8bebbcb3_63fa_47e0_bd08_43c40080b6a9_a1 M hM
  have hNcard :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_8bebbcb3_63fa_47e0_bd08_43c40080b6a9_a1 N hN hV hmax
  have hlt' : M.edgeSet.ncard + 6 < N.edgeSet.ncard + 6 := by omega
  have hne : N ≠ M := by
    intro h
    subst N
    exact (Nat.lt_irrefl _ hlt')
  exact ⟨N, hMN, hN, hne⟩