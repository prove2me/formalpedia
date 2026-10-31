-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:16:11.293639+00:00
-- url     : https://prove2.me/submissions/7e1614a1-0c68-4ca6-90cf-b5b10e02e8a6

import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K :=
  WilliamsonShmoys.planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1 H hH
