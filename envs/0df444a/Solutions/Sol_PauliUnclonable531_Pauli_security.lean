-- Prove2me | solution 1 for PauliUnclonable531.Pauli.security
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:52:04.712075+00:00
-- url     : https://prove2.me/submissions/97f7431b-44db-41ff-919c-49203fcc9614

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations
import Theorems.Thm_PauliUnclonable531_Pauli_ricochet
import Theorems.Thm_PauliUnclonable531_Pauli_top_eigenvalue
import Theorems.Thm_PauliUnclonable531_Pauli_filtered_product

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

open PauliUnclonable531.Pauli in
theorem solution {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Attack n B C) :
    win a ≤ 1/2 + (1/2) * Real.sqrt ((2 : ℝ)^n / ((4 : ℝ)^n - 1)) := by
  obtain ⟨d, -, -, -, -, hwin⟩ := ricochet n hn a
  have hγ : gamma n = (2 : ℝ)^n / ((4 : ℝ)^n - 1) := rfl
  set lam := largestEigenvalue (gameOperator d) with hlam
  have hsq := Real.sqrt_nonneg ((2 : ℝ)^n / ((4 : ℝ)^n - 1))
  by_cases hpos : 0 < lam
  · have h1 := top_eigenvalue n hn d hpos
    have h2 := filtered_product n hn d lam hpos
    rw [← hlam] at h1
    have hle : lam ≤ Real.sqrt ((2 : ℝ)^n / ((4 : ℝ)^n - 1)) := by
      rw [← hγ]
      exact Real.le_sqrt_of_sq_le (h1.trans h2)
    linarith
  · linarith
