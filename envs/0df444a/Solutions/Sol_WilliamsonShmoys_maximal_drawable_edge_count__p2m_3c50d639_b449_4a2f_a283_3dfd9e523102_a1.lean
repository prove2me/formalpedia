-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:11:43.980323+00:00
-- url     : https://prove2.me/submissions/54f71b65-391c-4a1d-9c02-b1458973c6c7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a3
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) [DecidableRel Q.Adj] (hQ : HasPlanarDrawingOn Q) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ (R : SimpleGraph V) (hRdec : DecidableRel R.Adj), Q ≤ R → HasPlanarDrawingOn R → R ≤ Q) : Q.edgeFinset.card + 6 = 3 * Fintype.card V := by
  classical
  obtain ⟨R, hQR, hRdraw, hRcount⟩ :=
    WilliamsonShmoys.planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a3
      Q hQ hcard
  have hRQ : R ≤ Q := hmax R (Classical.decRel _) hQR hRdraw
  have hEq : R = Q := le_antisymm hRQ hQR
  cases hEq
  simpa using hRcount