-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f9d76db2_d767_4642_99f4_dff7d260828e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:36:52.306035+00:00
-- url     : https://prove2.me/submissions/ed654bde-e97a-461b-84e4-b90f79f32768

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_identities__p2m_24cd5df2_f06e_484a_a9e0_671b5163ec2a_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M' : SimpleGraph V, M <= M' ->
      WilliamsonShmoys.HasPlanarDrawingOn M' -> M' = M) :
    3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
  obtain ⟨f, hfaces, heuler⟩ :=
    WilliamsonShmoys.maximal_planar_face_count_identities__p2m_24cd5df2_f06e_484a_a9e0_671b5163ec2a_a1
      M hplanar hcard hmax
  omega