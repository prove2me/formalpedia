-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:15:52.954467+00:00
-- url     : https://prove2.me/submissions/f4d27de4-c347-442d-9c8c-34d9a4c6eda0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_e5af1f58_1baf_49a9_bfe1_0313f8cb5edc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_e5af1f58_1baf_49a9_bfe1_0313f8cb5edc_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_e5af1f58_1baf_49a9_bfe1_0313f8cb5edc_a1
      K hK hcard
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_e5af1f58_1baf_49a9_bfe1_0313f8cb5edc_a1
      K hK hmax hcard
  omega