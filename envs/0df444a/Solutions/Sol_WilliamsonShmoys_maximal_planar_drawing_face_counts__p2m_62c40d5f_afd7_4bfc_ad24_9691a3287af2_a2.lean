-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_counts__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:20:05.150678+00:00
-- url     : https://prove2.me/submissions/7b04de4d-01dc-43e8-8e81-2b30165d294e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bounds__p2m_5f4b31de_07d6_4550_bc2e_2bb318dd0027_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by
  obtain ⟨hlower, hupper⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_edge_bounds__p2m_5f4b31de_07d6_4550_bc2e_2bb318dd0027_a1
      H hplanar hmax hcard
  let f : ℕ := H.edgeSet.ncard + 2 - Fintype.card V
  refine ⟨f, ?_, ?_⟩
  · dsimp [f]
    omega
  · dsimp [f]
    omega