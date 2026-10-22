-- Prove2me | solution 1 for ResolvingNRM.FRLower.lp_solution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:13:34.650183+00:00
-- url     : https://prove2.me/submissions/5aa5675f-d0fe-4db7-a585-6f406463e3b9

import Mathlib
import Definitions.Def_ResolvingNRM_FRLower_Instance

set_option autoImplicit false
open Matrix Finset ResolvingNRM.FRLower

theorem nrm_key (r₁ r₂ : ℝ) (hr₂ : 0 < r₂) (hr : r₂ < r₁) (b0 y0 y1 : ℝ)
    (hb : 0 ≤ b0) (h0 : 0 ≤ y0) (h1 : 0 ≤ y1) (h0' : y0 ≤ 1) (h1' : y1 ≤ 1) (hs : y0 + y1 ≤ b0) :
    r₁ * y0 + r₂ * y1 ≤ r₁ * min b0 1 + r₂ * min (max (b0 - 1) 0) 1 ∧
    (r₁ * y0 + r₂ * y1 = r₁ * min b0 1 + r₂ * min (max (b0 - 1) 0) 1 →
      y0 = min b0 1 ∧ y1 = min (max (b0 - 1) 0) 1) := by
  have hd : 0 < r₁ - r₂ := by linarith
  rcases le_or_gt b0 1 with hb1 | hb1
  · have e1 : min b0 1 = b0 := min_eq_left hb1
    have e2 : min (max (b0 - 1) 0) 1 = 0 := by
      rw [max_eq_right (by linarith)]; exact min_eq_left zero_le_one
    rw [e1, e2]
    refine ⟨by nlinarith, fun h => ?_⟩
    have : (r₁ - r₂) * y1 ≤ 0 := by nlinarith
    have hy1 : y1 = 0 := by
      by_contra hne
      have : 0 < y1 := lt_of_le_of_ne h1 (Ne.symm hne)
      nlinarith
    refine ⟨?_, hy1⟩
    rw [hy1] at h
    have : r₁ * (y0 - b0) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith
  rcases le_or_gt b0 2 with hb2 | hb2
  · have e1 : min b0 1 = 1 := min_eq_right hb1.le
    have e2 : min (max (b0 - 1) 0) 1 = b0 - 1 := by
      rw [max_eq_left (by linarith)]; exact min_eq_left (by linarith)
    rw [e1, e2]
    refine ⟨by nlinarith, fun h => ?_⟩
    have hA : 0 ≤ (r₁ - r₂) * (1 - y0) := mul_nonneg hd.le (by linarith)
    have hB : 0 ≤ r₂ * (b0 - y0 - y1) := mul_nonneg hr₂.le (by linarith)
    have hA0 : (r₁ - r₂) * (1 - y0) = 0 := by nlinarith
    have hB0 : r₂ * (b0 - y0 - y1) = 0 := by nlinarith
    have hy0 : y0 = 1 := by
      rcases mul_eq_zero.mp hA0 with h' | h'
      · linarith
      · linarith
    have hs' : b0 - y0 - y1 = 0 := by
      rcases mul_eq_zero.mp hB0 with h' | h'
      · linarith
      · exact h'
    exact ⟨hy0, by linarith⟩
  · have e1 : min b0 1 = 1 := min_eq_right (by linarith)
    have e2 : min (max (b0 - 1) 0) 1 = 1 := by
      rw [max_eq_left (by linarith)]; exact min_eq_right (by linarith)
    rw [e1, e2]
    refine ⟨by nlinarith, fun h => ?_⟩
    have hA : 0 ≤ r₁ * (1 - y0) := mul_nonneg (by linarith) (by linarith)
    have hB : 0 ≤ r₂ * (1 - y1) := mul_nonneg hr₂.le (by linarith)
    have hA0 : r₁ * (1 - y0) = 0 := by nlinarith
    have hB0 : r₂ * (1 - y1) = 0 := by nlinarith
    constructor
    · rcases mul_eq_zero.mp hA0 with h' | h'
      · linarith
      · linarith
    · rcases mul_eq_zero.mp hB0 with h' | h'
      · linarith
      · linarith

theorem solution (r₁ r₂ : ℝ) (hr₂ : 0 < r₂) (hr : r₂ < r₁)
    (b : Fin 1 → ℝ) (hb : 0 ≤ b 0) (x : Fin 2 → ℝ)
    (hx : IsDLPOptimal (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)) b x) :
    x 0 = min (b 0) 1 ∧ x 1 = min (max (b 0 - 1) 0) 1 := by
  obtain ⟨hfeas, hnn, hle, hval⟩ := hx
  have hA : ∀ y : Fin 2 → ℝ, ((twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)).A *ᵥ y) 0 = y 0 + y 1 := by
    intro y
    simp [twoClass, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hR : ∀ y : Fin 2 → ℝ, (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)).r ⬝ᵥ y = r₁ * y 0 + r₂ * y 1 := by
    intro y
    simp [twoClass, dotProduct, Fin.sum_univ_two]
  have hlam : (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)).lam = ![1, 1] := rfl
  have hlam0 : (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)).lam 0 = 1 := by simp [twoClass]
  have hlam1 : (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)).lam 1 = 1 := by simp [twoClass]
  have hfe : ∀ b0 : ℝ, 0 ≤ b0 → 0 ≤ min b0 1 ∧ min b0 1 ≤ 1 ∧ 0 ≤ min (max (b0 - 1) 0) 1 ∧
      min (max (b0 - 1) 0) 1 ≤ 1 ∧ min b0 1 + min (max (b0 - 1) 0) 1 ≤ b0 := by
    intro b0 hb0
    simp only [min_def, max_def]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> linarith
  set Vx : ℝ := r₁ * min (b 0) 1 + r₂ * min (max (b 0 - 1) 0) 1 with hV
  have hpi : RLPBidPrice.Unbiased.piValue (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)).A
      (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)).r b
      (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)).lam = Vx := by
    unfold RLPBidPrice.Unbiased.piValue
    apply IsGreatest.csSup_eq
    constructor
    · obtain ⟨f1, f2, f3, f4, f5⟩ := hfe (b 0) hb
      refine ⟨![min (b 0) 1, min (max (b 0 - 1) 0) 1], ?_, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        simp only [Fin.zero_eta, hA]
        simpa using f5
      · intro i
        fin_cases i
        · simpa using f1
        · simpa using f3
      · intro i
        fin_cases i
        · simpa [hlam0] using f2
        · simpa [hlam1] using f4
      · rw [hR]; simp [hV]
    · rintro v ⟨y, hy1, hy2, hy3, rfl⟩
      have a1 : y 0 + y 1 ≤ b 0 := by have := hy1 0; rwa [hA] at this
      have a2 : 0 ≤ y 0 := by simpa using hy2 0
      have a3 : 0 ≤ y 1 := by simpa using hy2 1
      have a4 : y 0 ≤ 1 := by have := hy3 0; rwa [hlam0] at this
      have a5 : y 1 ≤ 1 := by have := hy3 1; rwa [hlam1] at this
      rw [hR]
      exact (nrm_key r₁ r₂ hr₂ hr (b 0) (y 0) (y 1) hb a2 a3 a4 a5 a1).1
  have a1 : x 0 + x 1 ≤ b 0 := by have := hfeas 0; rwa [hA] at this
  have a2 : 0 ≤ x 0 := by simpa using hnn 0
  have a3 : 0 ≤ x 1 := by simpa using hnn 1
  have a4 : x 0 ≤ 1 := by have := hle 0; rwa [hlam0] at this
  have a5 : x 1 ≤ 1 := by have := hle 1; rwa [hlam1] at this
  rw [hpi, hR] at hval
  exact (nrm_key r₁ r₂ hr₂ hr (b 0) (x 0) (x 1) hb a2 a3 a4 a5 a1).2 hval
