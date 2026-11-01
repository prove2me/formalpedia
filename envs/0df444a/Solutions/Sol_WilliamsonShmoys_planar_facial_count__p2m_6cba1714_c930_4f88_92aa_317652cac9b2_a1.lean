-- Prove2me | solution 1 for WilliamsonShmoys.planar_facial_count__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:18:50.82959+00:00
-- url     : https://prove2.me/submissions/4480031f-a5f9-437d-a223-9ea327b92fa2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_euler_upper__p2m_2930c541_cd90_4895_988f_c75e47ffb674_a1
import Theorems.Thm_WilliamsonShmoys_planar_maximal_face_lower__p2m_2930c541_cd90_4895_988f_c75e47ffb674_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by
  obtain ⟨f, heuler, hupper⟩ :=
    WilliamsonShmoys.planar_euler_upper__p2m_2930c541_cd90_4895_988f_c75e47ffb674_a1
      H hplanar hmax hcard
  have hlower :=
    WilliamsonShmoys.planar_maximal_face_lower__p2m_2930c541_cd90_4895_988f_c75e47ffb674_a1
      H hplanar hmax hcard f heuler
  exact ⟨f, heuler, Nat.le_antisymm hupper hlower⟩