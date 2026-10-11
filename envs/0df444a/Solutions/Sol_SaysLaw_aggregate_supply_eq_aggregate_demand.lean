-- Prove2me | solution 1 for SaysLaw.aggregate_supply_eq_aggregate_demand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T20:04:14.890222+00:00
-- url     : https://prove2.me/submissions/93338068-29c6-42d1-b4c5-36738178f017

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_SaysLaw_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SaysLaw

theorem solution {ι G : Type*} [Fintype ι] [Fintype G]
    (p : G → ℝ) (supply demand : ι → G → ℝ)
    (hsay : SaysBudget p supply demand) :
    ∑ i, bundleValue p (demand i) = ∑ i, bundleValue p (supply i) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact hsay i
