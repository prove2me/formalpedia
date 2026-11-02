-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:17:15.917182+00:00
-- url     : https://prove2.me/submissions/2b1e495e-b7b5-4469-a69a-2951322375be

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1
import Theorems.Thm_SimpleGraph_edgeSet_ncard_mono__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1 G hG
  exact ⟨H, hGH, hH,
    SimpleGraph.edgeSet_ncard_mono__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1 G H hGH,
    hmax⟩