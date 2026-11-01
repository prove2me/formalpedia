-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:16:00.330171+00:00
-- url     : https://prove2.me/submissions/bbc2f7bb-868d-4482-8af6-c38b84779703
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_certificate__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
import Theorems.Thm_WilliamsonShmoys_face_count_arithmetic__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M' : SimpleGraph V, M <= M' ->
      WilliamsonShmoys.HasPlanarDrawingOn M' -> M' = M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  have hface :=
    WilliamsonShmoys.maximal_planar_drawing_face_certificate__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
      M hplanar hcard hmax
  exact Exists.elim hface (fun f hf =>
    Exists.elim hf (fun len hcert =>
      WilliamsonShmoys.face_count_arithmetic__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
        (Fintype.card V) M.edgeSet.ncard f len
        (And.left hcert) (And.left (And.right hcert))
        (And.right (And.right hcert))))