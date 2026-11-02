-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_face_count__p2m_1927a2f2_efe0_4e83_ba03_5beb334dbd6d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:14:36.008193+00:00
-- url     : https://prove2.me/submissions/f210bacf-59d9-45fe-8370-d6a3d6941282
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_842d51ec_371b_408a_a7fe_9c9e23312f53_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    ∃ f : ℕ,
      f + Fintype.card V = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  have hedge := WilliamsonShmoys.maximal_planar_edge_count__p2m_842d51ec_371b_408a_a7fe_9c9e23312f53_a1
    K hcard hplanar hmax
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega