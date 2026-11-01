-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximum_edge_supergraph__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:58:04.166783+00:00
-- url     : https://prove2.me/submissions/8d05d780-ab02-4f73-bcdc-8134d62ead19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_has_maximum_edges__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
      HasPlanarDrawingOn Q ∧ G ≤ Q ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        HasPlanarDrawingOn K →
        (letI : DecidableRel Q.Adj := dQ
         letI : DecidableRel K.Adj := dK
         Q.edgeFinset.card ≤ K.edgeFinset.card)) := by
  obtain ⟨Q, dQ, hQ, hGQ, hmaximal⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
      G dG hG
  refine ⟨Q, dQ, hQ, hGQ, ?_⟩
  intro K dK hK
  exact WilliamsonShmoys.inclusion_maximal_planar_has_maximum_edges__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
    Q dQ hQ hmaximal K dK hK