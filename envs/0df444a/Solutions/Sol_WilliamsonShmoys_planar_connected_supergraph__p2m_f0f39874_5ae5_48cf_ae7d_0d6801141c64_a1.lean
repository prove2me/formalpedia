-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:55:00.598514+00:00
-- url     : https://prove2.me/submissions/2ac93582-529b-4398-9e83-0b0ee6ec36e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      K.Connected ∧ HasPlanarDrawingOn K := by
  classical
  obtain ⟨K, hHK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2 H hH
  exact ⟨K, hHK,
    WilliamsonShmoys.maximal_planar_graph_connected__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2 K hKplanar hKmax,
    hKplanar⟩