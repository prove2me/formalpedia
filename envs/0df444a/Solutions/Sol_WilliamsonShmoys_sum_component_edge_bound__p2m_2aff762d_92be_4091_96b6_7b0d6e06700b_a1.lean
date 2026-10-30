-- Prove2me | solution 1 for WilliamsonShmoys.sum_component_edge_bound__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:56.72142+00:00
-- url     : https://prove2.me/submissions/b0717448-86f9-4abc-b84f-b742d65f31d1

import Mathlib
import Theorems.Thm_WilliamsonShmoys_sum_component_edge_bound_arithmetic__p2m_1501895e_8d06_4c19_968a_5139d07078f6_a1

set_option autoImplicit false

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hcomponents : ∀ (W : Finset V), 3 ≤ W.card →
      (M.induce (W : Set V)).Connected →
      (M.induce (W : Set V)).edgeSet.ncard + 6 ≤ 3 * W.card)
    (parts : Finset (Finset V))
    (hcard : Fintype.card V = ∑ W ∈ parts, W.card)
    (hedges : M.edgeSet.ncard =
      ∑ W ∈ parts, (M.induce (W : Set V)).edgeSet.ncard)
    (hconn : ∀ W ∈ parts, (M.induce (W : Set V)).Connected)
    (hsmall : ∀ W ∈ parts, W.card < 3 →
      (M.induce (W : Set V)).edgeSet.ncard ≤ W.card - 1) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have htotal : 3 ≤ ∑ W ∈ parts, W.card := by
    rw [← hcard]
    exact hV
  have h := WilliamsonShmoys.sum_component_edge_bound_arithmetic__p2m_1501895e_8d06_4c19_968a_5139d07078f6_a1
    parts
    (fun W => W.card)
    (fun W => (M.induce (W : Set V)).edgeSet.ncard)
    htotal
    (by
      intro W hW hlarge
      exact hcomponents W hlarge (hconn W hW))
    (by
      intro W hW hsmallW
      exact hsmall W hW hsmallW)
  rw [hedges, hcard]
  exact h