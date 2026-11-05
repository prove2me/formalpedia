-- Prove2me | solution 1 for WilliamsonShmoys.finite_drawable_supergraphs__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:38:12.298201+00:00
-- url     : https://prove2.me/submissions/8db565fd-8751-4816-a63c-594493d2052e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) :
    ({T : SimpleGraph V | L ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T}).Finite := by
  exact Set.toFinite _
