-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulated_edge_count__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:26:22.216883+00:00
-- url     : https://prove2.me/submissions/9866187c-6c43-4e11-a98f-3137ff993612
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
  have hupper : H.edgeFinset.card ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1 H hcard hdrawing
  have hlower : 3 * Fintype.card V - 6 ≤ H.edgeFinset.card :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1 H hcard hdrawing hmax
  omega