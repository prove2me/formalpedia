-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_exact_edge_count__p2m_f6ef00c3_9a62_41aa_bbc8_b32342398c0c_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:40.97826+00:00
-- url     : https://prove2.me/submissions/fa0ade33-c64f-4a69-975a-917a09910d25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_maximal_extension__p2m_7f97800d_a064_49bc_abdc_383c926e2440_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_maximal_edge_count__p2m_7f97800d_a064_49bc_abdc_383c926e2440_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    exists M : SimpleGraph V,
      LE.le L M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hMplanar, hmaximal⟩ :=
    WilliamsonShmoys.maximal_planar_completion_maximal_extension__p2m_7f97800d_a064_49bc_abdc_383c926e2440_a1
      L hLplanar
  exact ⟨M, hLM, hMplanar,
    WilliamsonShmoys.maximal_planar_completion_maximal_edge_count__p2m_7f97800d_a064_49bc_abdc_383c926e2440_a1
      M hMplanar hmaximal hV⟩