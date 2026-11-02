-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_strict_augmentation__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:06:54.288365+00:00
-- url     : https://prove2.me/submissions/15190712-d0d0-49f1-83f7-22200f9d7140
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_planar_supergraph__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hE : (letI : DecidableRel M.Adj := Classical.decRel M.Adj
           M.edgeFinset.card) < 3 * Fintype.card V - 6) :
    ∃ M' : SimpleGraph V, HasPlanarDrawingOn M' ∧ M ≤ M' ∧ M' ≠ M := by
  obtain ⟨M', hM', hle, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
      M hM
  have hEq : (letI : DecidableRel M'.Adj := Classical.decRel M'.Adj
      M'.edgeFinset.card) = 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
      M' hcard hM' hmax
  refine ⟨M', hM', hle, ?_⟩
  intro heq
  subst M'
  omega
