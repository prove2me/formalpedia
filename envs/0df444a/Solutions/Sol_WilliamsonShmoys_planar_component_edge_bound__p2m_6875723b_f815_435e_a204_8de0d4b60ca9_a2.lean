-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:47:45.968504+00:00
-- url     : https://prove2.me/submissions/b9f89886-6acc-4b91-bd39-c128f2d15373

import Theorems.Thm_WilliamsonShmoys_planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (c : K.ConnectedComponent) :
    letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
    letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
    (K.induce c.supp).edgeFinset.card ≤
      3 * Fintype.card {v : V // v ∈ c.supp} - 3 :=
  WilliamsonShmoys.planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3 K hK c