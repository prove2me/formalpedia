-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_b554ef36_a96a_42de_b297_4474260662ac_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:19:09.032133+00:00
-- url     : https://prove2.me/submissions/17297c8f-7bda-4fbc-ae42-75f20a6f7a03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_drawable_extension__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_drawable_extension__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
      H hH hcard
  refine ⟨K, hHK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
    K hK hcard hmax