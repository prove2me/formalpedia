-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_tight_edges__p2m_b575e78e_3e28_4118_93fc_258c931bc299_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:54:11.893193+00:00
-- url     : https://prove2.me/submissions/641f1c6a-fef5-4b26-abc3-153ea3034e7d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    ∃ P : SimpleGraph V,
      (∀ {u v : V}, N.Adj u v → P.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (letI : DecidableRel P.Adj := Classical.decRel P.Adj
       P.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨P, hNP, hP, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
      N hN
  refine ⟨P, hNP, hP, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
    P hP hcard hmax