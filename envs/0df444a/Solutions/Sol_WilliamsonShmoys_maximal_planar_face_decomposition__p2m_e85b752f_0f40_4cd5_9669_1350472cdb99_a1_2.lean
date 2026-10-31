-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_e85b752f_0f40_4cd5_9669_1350472cdb99_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:49:25.08329+00:00
-- url     : https://prove2.me/submissions/fa991f17-9e35-466d-a603-09eeaca3d9da

import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_and_incidence

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_euler_and_incidence H hplanar hmax hV
