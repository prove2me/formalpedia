-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_count_aggregation_induced_edge_count_sum.card_sigma_edge_sets
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:29.566382+00:00
-- url     : https://prove2.me/submissions/d6103dcc-8784-487c-93b0-a97496491f4b

import Mathlib
theorem solution
    {α β : Type} [Fintype β] (C : Finset β) (F : β → Type)
    [∀ b, Fintype (F b)] :
    Fintype.card (Σ b : C, F (b : β)) =
      C.sum (fun b => Fintype.card (F b)) := by
  rw [Fintype.card_sigma]
  exact Finset.sum_coe_sort C (fun b => Fintype.card (F b))
