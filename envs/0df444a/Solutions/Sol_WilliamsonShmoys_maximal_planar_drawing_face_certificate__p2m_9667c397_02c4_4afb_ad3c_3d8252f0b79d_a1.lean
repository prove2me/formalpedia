-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_certificate__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:26:35.472105+00:00
-- url     : https://prove2.me/submissions/18a7a1cc-298f-47dd-85ee-f2c1ea092e56

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_f9d76db2_d767_4642_99f4_dff7d260828e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_f9d76db2_d767_4642_99f4_dff7d260828e_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M' : SimpleGraph V, M <= M' ->
      WilliamsonShmoys.HasPlanarDrawingOn M' -> M' = M) :
    Exists (fun f : Nat => Exists (fun len : Fin f -> Nat =>
      (Fintype.card V + f = M.edgeSet.ncard + 2) /\
      (Finset.univ.sum (fun i : Fin f => len i) = 2 * M.edgeSet.ncard) /\
      (forall i : Fin f, len i = 3))) := by
  have hup := WilliamsonShmoys.planar_edge_upper_bound__p2m_f9d76db2_d767_4642_99f4_dff7d260828e_a1
    M hplanar hcard
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f9d76db2_d767_4642_99f4_dff7d260828e_a1
    M hplanar hcard hmax
  have he : M.edgeSet.ncard = 3 * Fintype.card V - 6 := by omega
  refine Exists.intro (2 * Fintype.card V - 4)
    (Exists.intro (fun _ => 3) (And.intro ?_ (And.intro ?_ ?_)))
  · omega
  · simp
    omega
  · intro i
    rfl