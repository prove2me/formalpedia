-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:08:32.813632+00:00
-- url     : https://prove2.me/submissions/c39678c2-c3aa-4822-ab89-768bacf4b62a

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_v2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧ M ≤ N ∧
      ∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K → N ≤ K → K = N :=
  WilliamsonShmoys.exists_maximal_planar_supergraph_v2 M hplanar