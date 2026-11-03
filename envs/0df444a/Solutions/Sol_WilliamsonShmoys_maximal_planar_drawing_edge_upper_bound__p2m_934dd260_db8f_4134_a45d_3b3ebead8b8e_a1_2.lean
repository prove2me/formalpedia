-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_934dd260_db8f_4134_a45d_3b3ebead8b8e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:53:33.411619+00:00
-- url     : https://prove2.me/submissions/22d20426-a1a1-4b47-aff7-697067c8449b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  have h := WilliamsonShmoys.planar_edge_count_bound__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2 K hK hcard
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at h
  exact h
