-- Prove2me | solution 1 for SupplyDemand.market_demand_strictAntiOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:13:53.010985+00:00
-- url     : https://prove2.me/submissions/5333bdc7-167f-4e9c-9d0c-a9af26320816

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_SupplyDemand_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SupplyDemand

theorem solution {ι : Type*} (I : Set ℝ) (s : Finset ι)
    (hs : s.Nonempty) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, StrictAntiOn (f i) I) :
    StrictAntiOn (marketCurve s f) I := by
  intro x hx y hy hxy
  change (∑ i ∈ s, f i y) < (∑ i ∈ s, f i x)
  exact Finset.sum_lt_sum_of_nonempty hs (fun i hi => hf i hi hx hy hxy)
