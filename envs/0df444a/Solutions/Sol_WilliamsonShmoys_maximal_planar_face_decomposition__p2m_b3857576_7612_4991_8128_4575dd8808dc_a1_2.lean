-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_b3857576_7612_4991_8128_4575dd8808dc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:47:34.141868+00:00
-- url     : https://prove2.me/submissions/b6b59b93-404d-44a6-9540-b6c3f5f604be

import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_and_incidence

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_euler_and_incidence M hM hMax hV
