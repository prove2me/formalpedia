-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulating_supergraph__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:37:00.061339+00:00
-- url     : https://prove2.me/submissions/79223c8c-31ea-485f-b9b8-57f88cc8bb7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
import Theorems.Thm_WilliamsonShmoys_edge_card_of_inclusion_maximal_planar__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card) = 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨H, hMH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
      M hM
  refine ⟨H, hMH, hH, ?_⟩
  exact WilliamsonShmoys.edge_card_of_inclusion_maximal_planar__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
    H hcard hH hmax