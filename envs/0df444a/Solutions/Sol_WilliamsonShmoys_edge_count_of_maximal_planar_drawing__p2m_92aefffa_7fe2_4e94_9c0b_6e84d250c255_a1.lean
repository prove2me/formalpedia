-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:35:49.702106+00:00
-- url     : https://prove2.me/submissions/110c42f1-3b9c-497c-ab7a-07bd4f3219f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_augmentation__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ M' : SimpleGraph V, HasPlanarDrawingOn M' → M ≤ M' → M' = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hupper := WilliamsonShmoys.planar_drawing_edge_bound__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
    M hcard hM
  have hlower : 3 * Fintype.card V - 6 ≤ M.edgeFinset.card := by
    by_contra h
    have hlt : M.edgeFinset.card < 3 * Fintype.card V - 6 := by omega
    obtain ⟨M', hM'draw, hsub, hne⟩ :=
      WilliamsonShmoys.planar_drawing_strict_augmentation__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
        M hcard hM hlt
    exact hne (hmax M' hM'draw hsub)
  omega
