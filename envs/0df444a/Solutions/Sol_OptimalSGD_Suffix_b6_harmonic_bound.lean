-- Prove2me | solution 1 for OptimalSGD.Suffix.b6_harmonic_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:57:43.207537+00:00
-- url     : https://prove2.me/submissions/5b4ff990-f167-4c56-b35f-c2be055a5e1c

import Mathlib
set_option autoImplicit false

theorem harm_aux (k : ℕ) (hk : 0 < k) (T : ℕ) (hT : k ≤ T) :
    ∑ t ∈ Finset.Icc (k + 1) T, (1 / (t : ℝ)) ≤ Real.log T - Real.log k := by
  induction T, hT using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hk hn)
    have h1 : Real.log ((n : ℝ) / (n + 1)) ≤ (n : ℝ) / (n + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hn0.ne' (by positivity)] at h1
    have h2 : (n : ℝ) / (n + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
      field_simp; ring
    push_cast
    linarith

theorem solution {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (T k : ℕ) (hT : 0 < T)
    (hk : (k : ℝ) = (1 - α) * T) :
    ∑ t ∈ Finset.Icc (k + 1) T, (1 / (t : ℝ)) ≤ Real.log (1 / (1 - α)) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hkpos : (0 : ℝ) < k := by rw [hk]; exact mul_pos (by linarith) hTr
  have hk0 : 0 < k := by exact_mod_cast hkpos
  have hkT : k ≤ T := by
    have : (k : ℝ) ≤ T := by rw [hk]; nlinarith
    exact_mod_cast this
  have h := harm_aux k hk0 T hkT
  have : Real.log (1 / (1 - α)) = Real.log T - Real.log k := by
    rw [← Real.log_div hTr.ne' hkpos.ne']
    congr 1
    rw [hk]; field_simp
  rw [this]; exact h
