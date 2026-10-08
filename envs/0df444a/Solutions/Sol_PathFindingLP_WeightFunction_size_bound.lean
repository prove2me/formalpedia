-- Prove2me | solution 1 for PathFindingLP.WeightFunction.size_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:41:19.804994+00:00
-- url     : https://prove2.me/submissions/d16e67df-341e-4421-a530-0f46e36eaa81

import Mathlib
import Definitions.Def_PathFindingLP_WeightFunction_RegularizedObjective

open Matrix PathFindingLP.WeightFunction in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (w : Fin m → ℝ) (hw : IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s w) :
    ∑ i, |w i| ≤ 2 * (A.rank : ℝ) := by
  obtain ⟨hwpos, hmin⟩ := hw
  have hrank : (A.rank : ℝ) = n := by exact_mod_cast hA
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmR : (n : ℝ) < m := by exact_mod_cast hnm
  have hmR : (0 : ℝ) < m := by linarith
  -- α > 0
  have hαpos : 0 < thm1Alpha A := by
    unfold thm1Alpha
    rw [hrank]
    have h2 : (2 : ℝ) < 2 * (m : ℝ) / n := by
      rw [lt_div_iff₀ hnR]; nlinarith
    have hL : 1 < Real.logb 2 (2 * (m : ℝ) / n) := by
      have := Real.logb_lt_logb (b := 2) (by norm_num) (by norm_num) h2
      rwa [Real.logb_self_eq_one (by norm_num)] at this
    have : (Real.logb 2 (2 * (m : ℝ) / n))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL
    linarith
  have hβm : thm1Beta A * m = n / 2 := by
    unfold thm1Beta; rw [hrank]; field_simp
  set α := thm1Alpha A with hαdef
  set β := thm1Beta A with hβdef
  have ht : (0 : ℝ) < 3 / 4 := by norm_num
  have key := hmin (fun i => (3 / 4 : ℝ) * w i) (fun i => mul_pos ht (hwpos i))
  unfold fhat at key
  set B := diagonal (fun i => (s i)⁻¹) * A with hB
  have hdiag : diagonal (fun i => ((3 / 4 : ℝ) * w i) ^ α)
      = ((3 / 4 : ℝ) ^ α) • diagonal (fun i => w i ^ α) := by
    ext i j
    rw [Matrix.smul_apply, diagonal_apply, diagonal_apply]
    split_ifs with h
    · subst h; rw [Real.mul_rpow ht.le (hwpos i).le]; rfl
    · simp
  have hdet : det (Bᵀ * diagonal (fun i => ((3 / 4 : ℝ) * w i) ^ α) * B)
      = ((3 / 4 : ℝ) ^ α) ^ n * det (Bᵀ * diagonal (fun i => w i ^ α) * B) := by
    rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.det_smul, Fintype.card_fin]
  rw [hdet] at key
  have hsum1 : ∑ i, (3 / 4 : ℝ) * w i = (3 / 4 : ℝ) * ∑ i, w i := by rw [Finset.mul_sum]
  have hlog : ∑ i, Real.log ((3 / 4 : ℝ) * w i)
      = m * Real.log (3 / 4 : ℝ) + ∑ i, Real.log (w i) := by
    have : ∀ i, Real.log ((3 / 4 : ℝ) * w i) = Real.log (3 / 4 : ℝ) + Real.log (w i) :=
      fun i => Real.log_mul (by norm_num) (hwpos i).ne'
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hsum1, hlog] at key
  set D := det (Bᵀ * diagonal (fun i => w i ^ α) * B) with hD
  set S := ∑ i, w i with hS
  set Lw := ∑ i, Real.log (w i) with hLw
  -- log (3/4) ≥ -1/3
  have hlt : -(1 / 3 : ℝ) ≤ Real.log (3 / 4 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    have h2 : Real.log (3 / 4 : ℝ) = - Real.log (4 / 3 : ℝ) := by
      rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hlneg : Real.log (3 / 4 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hSbound : S ≤ 2 * n := by
    by_cases hD0 : D = 0
    · rw [hD0, mul_zero, Real.log_zero] at key
      have hk : (1 / 4 : ℝ) * S ≤ -(β * m) * Real.log (3 / 4 : ℝ) := by nlinarith
      rw [hβm] at hk
      nlinarith
    · have hpow : ((3 / 4 : ℝ) ^ α) ^ n ≠ 0 := pow_ne_zero _ (Real.rpow_pos_of_pos ht _).ne'
      rw [Real.log_mul hpow hD0, Real.log_pow, Real.log_rpow ht] at key
      have hcancel : (1 / α) * ((n : ℝ) * (α * Real.log (3 / 4 : ℝ)))
          = n * Real.log (3 / 4 : ℝ) := by field_simp
      have hk : (1 / 4 : ℝ) * S ≤ -(n + β * m) * Real.log (3 / 4 : ℝ) := by
        have := key
        rw [mul_add, hcancel] at this
        nlinarith
      rw [hβm] at hk
      nlinarith
  have habs : ∑ i, |w i| = S := Finset.sum_congr rfl (fun i _ => abs_of_pos (hwpos i))
  rw [habs, hrank]
  exact hSbound
