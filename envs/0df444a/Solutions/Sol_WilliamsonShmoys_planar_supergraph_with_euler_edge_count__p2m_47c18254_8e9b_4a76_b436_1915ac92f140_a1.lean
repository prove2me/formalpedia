-- Prove2me | solution 1 for WilliamsonShmoys_planar_supergraph_with_euler_edge_count__p2m_47c18254_8e9b_4a76_b436_1915ac92f140_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:03.648454+00:00
-- url     : https://prove2.me/submissions/4a954886-287a-4f98-837b-cbca37913444
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_euler_edge_count__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeFinset ⊆ H.edgeFinset ∧
      H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨H, dH, hH, hLH, hmax⟩ :=
    WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
      L dL hL hcard
  have hcount :=
    WilliamsonShmoys_maximal_planar_graph_has_euler_edge_count__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
      H dH hH hcard hmax
  exact ⟨H, dH, hH, hLH, hcount⟩