-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:30:48.313007+00:00
-- url     : https://prove2.me/submissions/d9ed173c-fc0e-4dfb-8b1d-27d3dfcb7dbb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension__p2m_bba3ebb6_f48a_40f6_8fc3_19f0d2d80e0e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_bba3ebb6_f48a_40f6_8fc3_19f0d2d80e0e_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ K : SimpleGraph V,
      G.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_extension__p2m_bba3ebb6_f48a_40f6_8fc3_19f0d2d80e0e_a1
      G hcard hG
  refine ⟨K, hGK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_bba3ebb6_f48a_40f6_8fc3_19f0d2d80e0e_a1
    K hcard hK hmax