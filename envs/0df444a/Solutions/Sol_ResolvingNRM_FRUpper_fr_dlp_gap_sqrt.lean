-- Prove2me | solution 1 for ResolvingNRM.FRUpper.fr_dlp_gap_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:06:25.535067+00:00
-- url     : https://prove2.me/submissions/c306ddc1-b0d1-4d0f-816d-0a6d3f680a4b

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_FRUpper_Model
import Theorems.Thm_ResolvingNRM_FRUpper_fr_dlp_gap_explicit

open RLPBidPrice.Unbiased Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), ResolvingNRM.IRT.IsDLPSelector A r lam sel →
      ∀ T : ℕ, 1 ≤ T → ∀ C : Fin m → ℝ, 0 ≤ C →
        ResolvingNRM.IRT.dlpValue A r lam T C - ResolvingNRM.FRUpper.frValue A r lam sel T C
          ≤ M * Real.sqrt T := by
  set S := ∑ l, ResolvingNRM.FRUpper.rmaxRes A r l * ResolvingNRM.FRUpper.Kres A lam l
  set P := (n : ℝ) * ResolvingNRM.FRUpper.rMax r
  set Q := (n : ℝ) * ResolvingNRM.FRUpper.rMax r * ResolvingNRM.FRUpper.lamMax lam
  refine ⟨|S| * (2 + Real.sqrt 2) + 2 * |P| + |Q|, ?_⟩
  intro sel hsel T hT C hC
  have h := ResolvingNRM.FRUpper.fr_dlp_gap_explicit A r lam hlam hr hA sel hsel T hT C hC
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set s := Real.sqrt (T : ℝ) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hT1
  have hss : s * s = T := Real.mul_self_sqrt (by linarith)
  have hspos : 0 < s := by linarith
  -- log T ≤ 2 (s - 1)
  have hlog : Real.log T ≤ 2 * (s - 1) := by
    have : Real.log T = 2 * Real.log s := by
      rw [← hss, Real.log_mul hspos.ne' hspos.ne']; ring
    rw [this]
    have := Real.log_le_sub_one_of_pos hspos
    linarith
  have hlogpos : 0 ≤ Real.log T := Real.log_nonneg hT1
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have e1 : S * (2 * s + Real.sqrt 2) ≤ |S| * (2 + Real.sqrt 2) * s := by
    have a1 : S * (2 * s + Real.sqrt 2) ≤ |S| * (2 * s + Real.sqrt 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self S) (by positivity)
    have a2 : (2 * s + Real.sqrt 2) ≤ (2 + Real.sqrt 2) * s := by nlinarith
    have a3 : |S| * (2 * s + Real.sqrt 2) ≤ |S| * ((2 + Real.sqrt 2) * s) :=
      mul_le_mul_of_nonneg_left a2 (abs_nonneg S)
    linarith
  have e2 : P * (Real.log T + 1) ≤ 2 * |P| * s := by
    have a1 : P * (Real.log T + 1) ≤ |P| * (Real.log T + 1) :=
      mul_le_mul_of_nonneg_right (le_abs_self P) (by linarith)
    have a3 : |P| * (Real.log T + 1) ≤ |P| * (2 * s) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg P)
    linarith
  have e3 : Q ≤ |Q| * s := by
    have := le_abs_self Q
    have : |Q| ≤ |Q| * s := by
      have := mul_le_mul_of_nonneg_left hs1 (abs_nonneg Q); linarith
    linarith
  calc _ ≤ S * (2 * s + Real.sqrt 2) + P * (Real.log T + 1) + Q := h
    _ ≤ _ := by nlinarith
