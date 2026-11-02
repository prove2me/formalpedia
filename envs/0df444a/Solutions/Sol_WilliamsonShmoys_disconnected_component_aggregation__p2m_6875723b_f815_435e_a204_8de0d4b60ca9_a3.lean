-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_component_aggregation__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:27:05.44506+00:00
-- url     : https://prove2.me/submissions/47eac7cc-d1bb-47a2-88d7-6178bc573f04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_component_edges_le_sum__p2m_666f06c4_d624_4127_b254_b308e951621e_a1
import Theorems.Thm_WilliamsonShmoys_component_bounds_sum_le__p2m_666f06c4_d624_4127_b254_b308e951621e_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdisconn : ¬ K.Connected)
    (hcomponents : ∀ c : K.ConnectedComponent,
      letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
      letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
      (K.induce c.supp).edgeFinset.card ≤
        3 * Fintype.card {v : V // v ∈ c.supp} - 3) :
    letI : (L : SimpleGraph V) → DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  letI : Fintype K.ConnectedComponent := Fintype.ofFinite _
  letI : (L : SimpleGraph V) → DecidableRel L.Adj := fun L => Classical.decRel L.Adj
  calc
    K.edgeFinset.card ≤ ∑ c : K.ConnectedComponent,
        (letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
         (K.induce c.supp).edgeFinset.card) :=
      WilliamsonShmoys.component_edges_le_sum__p2m_666f06c4_d624_4127_b254_b308e951621e_a1 K
    _ ≤ ∑ c : K.ConnectedComponent,
        (letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
         3 * Fintype.card {v : V // v ∈ c.supp} - 3) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hcomponents c
    _ ≤ 3 * Fintype.card V - 6 :=
      WilliamsonShmoys.component_bounds_sum_le__p2m_666f06c4_d624_4127_b254_b308e951621e_a1 K hcard hdisconn