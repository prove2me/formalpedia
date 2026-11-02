-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_1d31a56b_8574_4be9_a710_fc2e7a582d14_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:28:04.973835+00:00
-- url     : https://prove2.me/submissions/1c95ce3e-fb22-4649-be3e-b458b452bfc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_count__p2m_e77a557c_0981_440f_93d6_d7c4c9434599_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_incidence__p2m_e77a557c_0981_440f_93d6_d7c4c9434599_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨f, hf⟩ := WilliamsonShmoys.maximal_planar_euler_face_count__p2m_e77a557c_0981_440f_93d6_d7c4c9434599_a1
    K hcard hK hmax
  have hinc := WilliamsonShmoys.maximal_planar_face_incidence__p2m_e77a557c_0981_440f_93d6_d7c4c9434599_a1
    K hcard hK hmax f hf
  omega