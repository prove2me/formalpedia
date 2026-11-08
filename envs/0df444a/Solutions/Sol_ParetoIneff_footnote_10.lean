-- Prove2me | solution 1 for ParetoIneff.footnote_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:09:12.595951+00:00
-- url     : https://prove2.me/submissions/8fd267ae-456d-4430-be28-abe4c0e181d7

import Mathlib
import Definitions.Def_ParetoIneff_Mech_IsEq
import Definitions.Def_ParetoIneff_Mech_IsComponents
import Definitions.Def_ParetoIneff_SingleTaskMech_IsEq

open NNReal

namespace ParetoIneff.Aux_PI

open ParetoIneff

theorem col_update {n m : ℕ} (s : Fin n → Fin m → ℝ≥0) (i : Fin n) (s' : Fin m → ℝ≥0)
    (k : Fin m) : col (Function.update s i s') k = Function.update (col s k) i (s' k) := by
  funext l
  by_cases h : l = i
  · subst h; simp [col]
  · simp [col, Function.update_of_ne h]

theorem util_eq {n : ℕ} (M : Mech n) (m : ℕ) (A : Fin m → SingleTaskMech n)
    (hA : M.IsComponents m A) (t s : Fin n → Fin m → ℝ≥0) (i : Fin n) :
    M.utility m t s i = ∑ j, (A j).utility (col t j) (col s j) i := by
  unfold Mech.utility SingleTaskMech.utility MatousekLP.Scheduling.load
  rw [(hA s).2 i, Finset.sum_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [(hA s).1 j]
  simp [costMatrix, col]

end ParetoIneff.Aux_PI

open ParetoIneff ParetoIneff.Aux_PI in
theorem solution {n : ℕ} (M : Mech n) (m : ℕ) (A : Fin m → SingleTaskMech n)
    (hA : M.IsComponents m A) (t s : Fin n → Fin m → ℝ≥0) :
    M.IsEq m t s ↔ ∀ j : Fin m, (A j).IsEq (col t j) (col s j) := by
  constructor
  · intro h j i b
    have hi := h i (Function.update (s i) j b)
    rw [util_eq M m A hA, util_eq M m A hA] at hi
    simp only [col_update] at hi
    have key : ∑ k, (A k).utility (col t k)
          (Function.update (col s k) i (Function.update (s i) j b k)) i -
        ∑ k, (A k).utility (col t k) (col s k) i =
        (A j).utility (col t j) (Function.update (col s j) i b) i -
          (A j).utility (col t j) (col s j) i := by
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single j]
      · rw [Function.update_self]
      · intro k _ hk
        rw [Function.update_of_ne hk]
        have : Function.update (col s k) i (s i k) = col s k :=
          Function.update_eq_self i (col s k)
        rw [this, sub_self]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    linarith
  · intro h i s'
    rw [util_eq M m A hA, util_eq M m A hA]
    apply Finset.sum_le_sum
    intro k _
    rw [col_update]
    exact h k i (s' k)
