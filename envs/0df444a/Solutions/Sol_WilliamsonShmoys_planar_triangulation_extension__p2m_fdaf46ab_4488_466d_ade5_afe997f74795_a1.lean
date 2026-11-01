-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_fdaf46ab_4488_466d_ade5_afe997f74795_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:23.137146+00:00
-- url     : https://prove2.me/submissions/fc8b0b26-0fe7-416f-b69d-7270b64e806f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_exists__p2m_6387f002_1fd9_417d_811a_77c2c095c6e5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6387f002_1fd9_417d_811a_77c2c095c6e5_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    ∃ H : SimpleGraph V,
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       G.edgeFinset.card <= H.edgeFinset.card) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨H, hGH, hH, hcardGH, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension_exists__p2m_6387f002_1fd9_417d_811a_77c2c095c6e5_a1
      G hG
  have hformula :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_6387f002_1fd9_417d_811a_77c2c095c6e5_a1
      H hH hcard hmax
  exact ⟨H, hcardGH, hH, hformula⟩