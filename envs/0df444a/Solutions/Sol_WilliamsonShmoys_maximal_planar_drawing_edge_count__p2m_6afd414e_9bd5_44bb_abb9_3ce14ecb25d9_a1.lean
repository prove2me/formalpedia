-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:01:45.315248+00:00
-- url     : https://prove2.me/submissions/1e200b59-09c6-44c6-b446-1a9fd1b0d8b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_counts__p2m_d4ee878b_f197_42bb_afe9_c773b884d027_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, htri⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_counts__p2m_d4ee878b_f197_42bb_afe9_c773b884d027_a1
      H hH hmax hcard
  omega