-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_independent_of_decidableRel__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:35.831785+00:00
-- url     : https://prove2.me/submissions/9cf4d840-e443-4a9e-91f1-d03a1647b5b1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (d1 d2 : DecidableRel G.Adj) :
    (letI : DecidableRel G.Adj := d1; G.edgeFinset.card) =
      (letI : DecidableRel G.Adj := d2; G.edgeFinset.card) := by
  have h : d1 = d2 := Subsingleton.elim _ _
  cases h
  rfl