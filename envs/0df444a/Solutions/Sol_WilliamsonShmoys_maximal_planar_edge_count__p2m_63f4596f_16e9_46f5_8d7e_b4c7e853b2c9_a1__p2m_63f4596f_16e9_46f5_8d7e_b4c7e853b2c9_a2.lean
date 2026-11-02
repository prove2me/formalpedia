-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:32:55.478915+00:00
-- url     : https://prove2.me/submissions/239aee25-e269-4bcd-8fbf-0c8bb3d84329
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hLower⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_lower_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a1
      G hcard hG
  have hKG : K = G := hmax K hGK hK
  subst K
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_a182218b_7bb5_40ee_89de_81ca71397f53_a2
      G hcard hG
  omega