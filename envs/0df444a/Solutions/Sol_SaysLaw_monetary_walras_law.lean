-- Prove2me | solution 1 for SaysLaw.monetary_walras_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T20:06:01.646398+00:00
-- url     : https://prove2.me/submissions/3520d165-985e-4697-ad00-0045acf1c0da

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_SaysLaw_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SaysLaw

private theorem says_value_excess {ι G : Type*} [Fintype ι] [Fintype G]
    (p : G → ℝ) (supply demand : ι → G → ℝ) :
    bundleValue p (excessDemand supply demand) =
      ∑ i, (bundleValue p (demand i) - bundleValue p (supply i)) := by
  calc
    bundleValue p (excessDemand supply demand) =
        ∑ g, ∑ i, p g * (demand i g - supply i g) := by
          simp only [bundleValue, excessDemand, Finset.mul_sum]
    _ = ∑ i, ∑ g, p g * (demand i g - supply i g) := Finset.sum_comm
    _ = ∑ i, (bundleValue p (demand i) - bundleValue p (supply i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [bundleValue, mul_sub, Finset.sum_sub_distrib]

theorem solution {ι G : Type*} [Fintype ι] [Fintype G]
    (p : G → ℝ) (supply demand : ι → G → ℝ) (m m' : ι → ℝ)
    (hbudget : MonetaryBudget p supply demand m m') :
    bundleValue p (excessDemand supply demand) +
      excessMoneyDemand m m' = 0 := by
  rw [says_value_excess]
  change (∑ i, (bundleValue p (demand i) - bundleValue p (supply i))) +
    (∑ i, (m' i - m i)) = 0
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  have hb := hbudget i
  change bundleValue p (demand i) + m' i =
    bundleValue p (supply i) + m i at hb
  linarith
