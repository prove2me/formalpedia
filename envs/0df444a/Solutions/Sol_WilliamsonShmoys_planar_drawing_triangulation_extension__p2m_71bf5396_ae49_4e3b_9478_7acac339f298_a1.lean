-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_71bf5396_ae49_4e3b_9478_7acac339f298_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:31:49.927199+00:00
-- url     : https://prove2.me/submissions/cd4d0a9d-739f-4d7a-ade6-ade5f994c8ef

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V, T ≤ U ∧ HasPlanarDrawingOn U ∧
      (letI : DecidableRel U.Adj := Classical.decRel U.Adj
       3 * Fintype.card V = U.edgeFinset.card + 6) := by
  obtain ⟨U, hTU, hU, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation T hT hcard
  refine ⟨U, hTU, hU, ?_⟩
  classical
  have hconvert : U.edgeFinset.card = U.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card]
    exact Set.fintypeCard_eq_ncard U.edgeSet
  rw [hconvert]
  exact hcount