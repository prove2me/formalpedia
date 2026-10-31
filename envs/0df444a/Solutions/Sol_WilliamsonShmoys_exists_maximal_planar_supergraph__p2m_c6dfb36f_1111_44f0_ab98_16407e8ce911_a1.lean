-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_c6dfb36f_1111_44f0_ab98_16407e8ce911_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:45:41.715254+00:00
-- url     : https://prove2.me/submissions/454ce8fa-6857-43f4-8935-31d7162d3d05

import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K :=
  WilliamsonShmoys.planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1 H hH
