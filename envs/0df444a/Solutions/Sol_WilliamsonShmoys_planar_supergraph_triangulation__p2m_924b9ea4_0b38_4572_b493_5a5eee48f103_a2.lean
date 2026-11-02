-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_924b9ea4_0b38_4572_b493_5a5eee48f103_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:10:25.141192+00:00
-- url     : https://prove2.me/submissions/f6037781-6ed1-48b5-93c6-73d7cbc5808a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    ∃ L : SimpleGraph V,
      K.edgeFinset ⊆ L.edgeFinset ∧
      HasPlanarDrawingOn L ∧
      L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : ∀ L : SimpleGraph V, DecidableRel L.Adj :=
    fun L => Classical.decRel L.Adj
  obtain ⟨L, hsub, hdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2 K hK
  refine ⟨L, hsub, hdraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2 K L hcard ⟨hsub, hdraw, hmax⟩
