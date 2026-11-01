-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_of_card_ge_three__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:05:29.858083+00:00
-- url     : https://prove2.me/submissions/6164b8f3-c2ac-400b-a0e0-76bd86f7958e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_count__p2m_b3780c9f_7548_4d87_b8fb_1d68dbe20f67_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.maximal_planar_euler_face_count__p2m_b3780c9f_7548_4d87_b8fb_1d68dbe20f67_a1
      M hplanar hmax hcard
  omega