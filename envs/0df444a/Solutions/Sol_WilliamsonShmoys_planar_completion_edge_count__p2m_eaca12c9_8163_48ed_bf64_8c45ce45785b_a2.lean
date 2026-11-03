-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:50:00.753701+00:00
-- url     : https://prove2.me/submissions/8ac3cde5-9b27-4156-993e-51a18e78d9f7

import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hQ : HasPlanarDrawingOn Q) (hcard : 3 ≤ Fintype.card V) : ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧ ∀ [hRdec : DecidableRel R.Adj], R.edgeFinset.card + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a3 Q hQ hcard