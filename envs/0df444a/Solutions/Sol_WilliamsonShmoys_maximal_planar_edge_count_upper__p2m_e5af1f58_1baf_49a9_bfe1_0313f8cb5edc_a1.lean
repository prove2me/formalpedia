-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_e5af1f58_1baf_49a9_bfe1_0313f8cb5edc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:28:40.886394+00:00
-- url     : https://prove2.me/submissions/c4bc010b-b36f-4909-970d-c74802a1df82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_exact__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeFinset_card_mono__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
      K hK
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_exact__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
      H hH hmax hcard
  have hmono :=
    WilliamsonShmoys.simpleGraph_edgeFinset_card_mono__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
      K H hKH
  rw [hcount] at hmono
  exact hmono