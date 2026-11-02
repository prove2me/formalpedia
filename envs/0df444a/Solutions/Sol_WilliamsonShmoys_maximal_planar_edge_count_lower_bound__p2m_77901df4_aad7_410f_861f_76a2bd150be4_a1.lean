-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:45:22.961192+00:00
-- url     : https://prove2.me/submissions/6200ecc5-3a47-4f6c-906c-4354439114cd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_v10

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall L : SimpleGraph V, G <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L <= G) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    3 * Fintype.card V <= G.edgeFinset.card + 6 := by
  classical
  have hcard : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard]
  have h :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_v10 G hV hG hmax
  rw [← hcard] at h
  exact h
