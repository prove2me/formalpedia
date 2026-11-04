-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_with_exact_edge_count__p2m_126d21f0_5b15_4e81_98d4_afc1d569f5a6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:39:09.587096+00:00
-- url     : https://prove2.me/submissions/0c9bd27c-dcb9-4992-a77d-751856f3ecd4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_has_exact_edge_count__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       K.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨K, hGK, hPlanar, hMaximal⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
      G hG
  refine ⟨K, hGK, hPlanar, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_has_exact_edge_count__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
    K hV hPlanar hMaximal