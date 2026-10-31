-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_12adc1a9_2da3_4bce_a578_d16f94d48e85_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:27:08.919036+00:00
-- url     : https://prove2.me/submissions/6db1d152-4db4-48fe-8847-8f618f1ad764

import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K :=
  WilliamsonShmoys.planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1 H hH
