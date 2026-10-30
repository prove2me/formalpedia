-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:05:13.879182+00:00
-- url     : https://prove2.me/submissions/5f404c41-1764-45fd-9afd-6cf6bac08290
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ H : SimpleGraph V,
      U.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  have hbound :=
    WilliamsonShmoys.planar_drawing_edge_bound__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
      U hV hU
  obtain ⟨H, hconn, hdraw, hcard⟩ :=
    WilliamsonShmoys.exists_planar_triangulation__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
      (V := V) hV
  refine ⟨H, ?_, hconn, hdraw⟩
  omega