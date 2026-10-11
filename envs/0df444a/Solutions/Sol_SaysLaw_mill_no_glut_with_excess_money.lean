-- Prove2me | solution 1 for SaysLaw.mill_no_glut_with_excess_money
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T20:25:37.520101+00:00
-- url     : https://prove2.me/submissions/0dbb30fd-1b39-4fb2-a396-3e7148d10667

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

theorem solution {ι G : Type*} [Fintype ι] [Fintype G] [Nonempty G]
    (p : G → ℝ) (hp : ∀ g, 0 < p g) (supply demand : ι → G → ℝ)
    (m m' : ι → ℝ) (hbudget : MonetaryBudget p supply demand m m') :
    ¬ (GeneralGlut (excessDemand supply demand) ∧
      excessMoneyDemand m m' ≤ 0) := by
  have hv : bundleValue p (excessDemand supply demand) +
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
  rintro ⟨hglut, hmoney⟩
  have hn : bundleValue p (excessDemand supply demand) < 0 := by
    change (∑ g, p g * excessDemand supply demand g) < 0
    have hle : ∀ g ∈ (Finset.univ : Finset G),
        p g * excessDemand supply demand g ≤ (0 : ℝ) := by
      intro g hg
      exact (mul_neg_of_pos_of_neg (hp g) (hglut g)).le
    have hstr : ∃ g ∈ (Finset.univ : Finset G),
        p g * excessDemand supply demand g < (0 : ℝ) := by
      obtain ⟨g⟩ := (inferInstance : Nonempty G)
      exact ⟨g, Finset.mem_univ _, mul_neg_of_pos_of_neg (hp g) (hglut g)⟩
    have hlt : (∑ g, p g * excessDemand supply demand g) <
        ∑ g, (0 : ℝ) := Finset.sum_lt_sum hle hstr
    simpa using hlt
  linarith
