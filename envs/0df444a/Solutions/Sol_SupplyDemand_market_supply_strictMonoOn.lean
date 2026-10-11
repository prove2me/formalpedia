-- Prove2me | solution 1 for SupplyDemand.market_supply_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:13:08.383469+00:00
-- url     : https://prove2.me/submissions/c84839ae-a671-4e9c-af3d-42c66cc81785

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_SupplyDemand_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SupplyDemand

theorem solution {ι : Type*} (I : Set ℝ) (s : Finset ι)
    (hs : s.Nonempty) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, StrictMonoOn (f i) I) :
    StrictMonoOn (marketCurve s f) I := by
  intro x hx y hy hxy
  change (∑ i ∈ s, f i x) < (∑ i ∈ s, f i y)
  exact Finset.sum_lt_sum_of_nonempty hs (fun i hi => hf i hi hx hy hxy)
