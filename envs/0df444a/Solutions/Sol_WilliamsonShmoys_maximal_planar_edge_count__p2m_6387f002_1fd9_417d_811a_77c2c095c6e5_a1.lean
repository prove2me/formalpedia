-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6387f002_1fd9_417d_811a_77c2c095c6e5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:16.468693+00:00
-- url     : https://prove2.me/submissions/0c6523bb-d40d-44ef-9be4-96ac16dc5703
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_upper_bound__p2m_8514b45e_f592_4fc5_88fb_d0f4ef7fe022_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_bound__p2m_8514b45e_f592_4fc5_88fb_d0f4ef7fe022_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hu : H.edgeFinset.card + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_upper_bound__p2m_8514b45e_f592_4fc5_88fb_d0f4ef7fe022_a1
      H hH hcard
  have hl : 3 * Fintype.card V ≤ H.edgeFinset.card + 6 :=
    WilliamsonShmoys.maximal_planar_lower_bound__p2m_8514b45e_f592_4fc5_88fb_d0f4ef7fe022_a1
      H hH hcard hmax
  omega