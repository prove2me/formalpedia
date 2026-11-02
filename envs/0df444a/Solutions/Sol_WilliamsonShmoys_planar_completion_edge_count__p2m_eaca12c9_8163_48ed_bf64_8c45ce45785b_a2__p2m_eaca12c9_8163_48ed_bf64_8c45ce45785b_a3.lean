-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a2__p2m_eaca12c9_8163_48ed_bf64_8c45ce45785b_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:38:32.922687+00:00
-- url     : https://prove2.me/submissions/e262e345-737b-4221-a508-a1e35600cd7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_extension__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1
import Mathlib
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hQ : HasPlanarDrawingOn Q)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧
      ∀ [hRdec : DecidableRel R.Adj],
        R.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨R, hQR, hR, hmax⟩ :=
    WilliamsonShmoys.planar_edge_maximal_extension__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1
      Q hQ hcard
  refine ⟨R, hQR, hR, ?_⟩
  intro hRdec
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1
    R hR hcard hmax