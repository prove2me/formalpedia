-- Prove2me | solution 1 for RobustSAA.Discrete.chi_tv_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:36:19.082069+00:00
-- url     : https://prove2.me/submissions/f89800cc-1a99-496c-8a19-7092b005f10e

import Definitions.Def_RobustSAA_Discrete_Setting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators ENNReal
open MeasureTheory Finset RobustSAA.Discrete

theorem solution {n N : ℕ} (F₀ : ProbabilityMeasure (Fin n))
    (s : Fin N → Fin n) :
    ENNReal.ofReal (dTV (phat s) (pvec F₀)) ≤ chiStat F₀ s / 2 := by
  classical
  let p := pvec F₀
  let q := phat s
  have hp (j : Fin n) : 0 ≤ p j := measureReal_nonneg
  have hsum : ∑ j, p j = 1 := by
    simpa [p, pvec, Measure.real]
      using (sum_measureReal_singleton (μ := (F₀ : Measure (Fin n))) (univ : Finset (Fin n)))
  by_cases hbad : ∃ j, p j = 0 ∧ q j ≠ 0
  · obtain ⟨j, hpj, hqj⟩ := hbad
    have ht : ENNReal.ofReal ((p j - q j) ^ 2) / ENNReal.ofReal (p j) = ⊤ := by
      rw [hpj, ENNReal.ofReal_zero]
      exact ENNReal.div_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero (by simpa using hqj))))
    have hs : (∑ j : Fin n, ENNReal.ofReal ((p j - q j) ^ 2) / ENNReal.ofReal (p j)) = ⊤ := by
      exact ENNReal.sum_eq_top.mpr ⟨j, mem_univ j, ht⟩
    have hchi : chiStat F₀ s = ⊤ := by
      change (∑ j : Fin n, ENNReal.ofReal ((p j - q j) ^ 2) / ENNReal.ofReal (p j)) ^ (1 / 2 : ℝ) = ⊤
      rw [hs, ENNReal.top_rpow_of_pos (by positivity)]
    rw [hchi, ENNReal.top_div_of_ne_top (by norm_num)]
    exact le_top
  have hzero (j : Fin n) (hj : p j = 0) : q j = 0 := by
    by_contra hq
    exact hbad ⟨j,hj,hq⟩
  let t : Fin n → ℝ := fun j => (p j - q j) ^ 2 / p j
  have ht (j : Fin n) : 0 ≤ t j := div_nonneg (sq_nonneg _) (hp j)
  have hpoint (j : Fin n) : |q j - p j| ^ 2 ≤ t j * p j := by
    by_cases hj : p j = 0
    · simp [hj, hzero j hj, t]
    · dsimp [t]
      rw [div_mul_cancel₀ _ hj, sq_abs]
      exact le_of_eq (by ring)
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (fun j _ => ht j) (fun j _ => hp j) (fun j _ => hpoint j)
  rw [hsum, mul_one] at hcs
  have hreal : dTV q p ≤ Real.sqrt (∑ j, t j) / 2 := by
    have hroot := Real.le_sqrt_of_sq_le hcs
    dsimp [dTV]
    linarith
  have hterm (j : Fin n) : ENNReal.ofReal ((p j - q j) ^ 2) / ENNReal.ofReal (p j) =
      ENNReal.ofReal (t j) := by
    by_cases hj : p j = 0
    · simp [hj, hzero j hj, t]
    · exact (ENNReal.ofReal_div_of_pos (lt_of_le_of_ne (hp j) (Ne.symm hj))).symm
  have hchi : chiStat F₀ s = ENNReal.ofReal (Real.sqrt (∑ j, t j)) := by
    change (∑ j : Fin n, ENNReal.ofReal ((p j - q j) ^ 2) / ENNReal.ofReal (p j)) ^ (1 / 2 : ℝ) = _
    simp_rw [hterm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => ht j)]
    rw [ENNReal.ofReal_rpow_of_nonneg (sum_nonneg (fun j _ => ht j)) (by positivity), ← Real.sqrt_eq_rpow]
  rw [hchi, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact ENNReal.ofReal_le_ofReal hreal

#print axioms solution



