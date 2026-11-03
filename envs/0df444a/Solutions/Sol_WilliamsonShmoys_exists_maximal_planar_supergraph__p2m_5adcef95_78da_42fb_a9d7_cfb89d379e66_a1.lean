-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:32:21.349267+00:00
-- url     : https://prove2.me/submissions/7b182d85-d42d-4e72-ae0d-7c4932a56c76

import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ H : SimpleGraph V, L ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L :=
  WilliamsonShmoys.maximal_planar_extension_exists__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2 G hG