-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_drawable_supergraph__p2m_dedf5137_e1df_470f_a755_e725cf271f52_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:47:46.244515+00:00
-- url     : https://prove2.me/submissions/cfefa7dd-c262-41a2-8be2-02bcc87801b7

import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K :=
  WilliamsonShmoys.maximal_planar_supergraph G hDraw
