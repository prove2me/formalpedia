-- Prove2me | solution 1 for WilliamsonShmoys.component_support_ncard_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:41:29.481198+00:00
-- url     : https://prove2.me/submissions/99e52ae9-c54c-4a57-9edc-af20cc1a5e9f

import Mathlib
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    (∑ C : K.ConnectedComponent, C.supp.ncard) = Fintype.card V := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
    (f := K.connectedComponentMk) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr (by ext; simp) fun C _ => ?_
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
