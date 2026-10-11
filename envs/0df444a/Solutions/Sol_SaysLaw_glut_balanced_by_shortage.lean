-- Prove2me | solution 1 for SaysLaw.glut_balanced_by_shortage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T20:06:36.004479+00:00
-- url     : https://prove2.me/submissions/3647a3a1-b6e0-4689-a6cd-030e66a1324e

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

theorem solution {ι G : Type*} [Fintype ι] [Fintype G]
    (p : G → ℝ) (hp : ∀ g, 0 < p g) (supply demand : ι → G → ℝ)
    (hsay : SaysBudget p supply demand) (g₀ : G)
    (hglut : excessDemand supply demand g₀ < 0) :
    ∃ g, g ≠ g₀ ∧ 0 < excessDemand supply demand g := by
  have hv : bundleValue p (excessDemand supply demand) = 0 := by
    rw [says_value_excess]
    apply Finset.sum_eq_zero
    intro i hi
    exact sub_eq_zero.mpr (hsay i)
  by_contra hno
  have hle : ∀ g ∈ (Finset.univ : Finset G),
      p g * excessDemand supply demand g ≤ (0 : ℝ) := by
    intro g hg
    have hz : excessDemand supply demand g ≤ 0 := by
      by_cases he : g = g₀
      · simpa [he] using le_of_lt hglut
      · have hh : ¬ 0 < excessDemand supply demand g := by
          intro hh
          exact hno ⟨g, he, hh⟩
        exact le_of_not_gt hh
    exact mul_nonpos_of_nonneg_of_nonpos (hp g).le hz
  have hstr : ∃ g ∈ (Finset.univ : Finset G),
      p g * excessDemand supply demand g < (0 : ℝ) :=
    ⟨g₀, Finset.mem_univ _, mul_neg_of_pos_of_neg (hp g₀) hglut⟩
  have hn : (∑ g, p g * excessDemand supply demand g) < (0 : ℝ) := by
    have hh : (∑ g, p g * excessDemand supply demand g) <
        ∑ g, (0 : ℝ) := Finset.sum_lt_sum hle hstr
    simpa using hh
  change (∑ g, p g * excessDemand supply demand g) = 0 at hv
  linarith
