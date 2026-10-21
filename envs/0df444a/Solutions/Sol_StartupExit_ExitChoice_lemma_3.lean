-- Prove2me | solution 1 for StartupExit.ExitChoice.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:33:09.159068+00:00
-- url     : https://prove2.me/submissions/73d44a7a-1998-4d19-8de8-0f4d0cf487ef

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_OrderStats

set_option autoImplicit false
open StartupExit.ExitChoice

lemma hasDerivAt_H (x : ℝ) : HasDerivAt H (1 / 2 : ℝ) x := by
  have := ((hasDerivAt_id x).add_const (1 : ℝ)).div_const 2
  have e : H = fun x => (x + 1) / 2 := rfl
  rw [e]
  simpa using this

lemma hasDerivAt_Hpow (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => H y ^ (k + 1)) (((k : ℝ) + 1) * H x ^ k / 2) x := by
  refine ((hasDerivAt_H x).pow (k + 1)).congr_deriv ?_
  simp; ring

lemma H_one : H 1 = 1 := by simp [H]
lemma H_neg_one : H (-1) = 0 := by simp [H]

lemma cont_H : Continuous H := by unfold H; fun_prop

lemma X1_eq (n : ℕ) : X1 (n + 1) = (((n + 1 : ℕ) : ℝ) - 1) / (((n + 1 : ℕ) : ℝ) + 1) := by
  unfold X1
  have hd : ∀ x ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun y => y * H y ^ (n + 1) - 2 / ((n : ℝ) + 2) * H y ^ (n + 2))
        (x * fdens x (n + 1)) x := by
    intro x _
    have h1 := (hasDerivAt_id x).mul (hasDerivAt_Hpow n x)
    have h2 := (hasDerivAt_Hpow (n + 1) x).const_mul (2 / ((n : ℝ) + 2))
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    simp [fdens, h]
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp only [H_one, H_neg_one]
    push_cast
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    unfold fdens h
    have := cont_H
    fun_prop

lemma X2_eq (n : ℕ) : X2 (n + 2) = (((n + 2 : ℕ) : ℝ) - 3) / (((n + 2 : ℕ) : ℝ) + 1) := by
  unfold X2
  have hd : ∀ x ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun y => y * (((n : ℝ) + 2) * H y ^ (n + 1) - ((n : ℝ) + 1) * H y ^ (n + 2))
          - 2 * (H y ^ (n + 2) - ((n : ℝ) + 1) / ((n : ℝ) + 3) * H y ^ (n + 3)))
        (x * gdens x (n + 2)) x := by
    intro x _
    have hA := hasDerivAt_Hpow n x
    have hB := hasDerivAt_Hpow (n + 1) x
    have hC := hasDerivAt_Hpow (n + 2) x
    have hG := (hA.const_mul ((n : ℝ) + 2)).sub (hB.const_mul ((n : ℝ) + 1))
    have h1 := (hasDerivAt_id x).mul hG
    have hI := (hB.sub (hC.const_mul (((n : ℝ) + 1) / ((n : ℝ) + 3)))).const_mul 2
    have h3 := h1.sub hI
    have h4 : HasDerivAt (fun y => y * (((n : ℝ) + 2) * H y ^ (n + 1) - ((n : ℝ) + 1) * H y ^ (n + 2))
          - 2 * (H y ^ (n + 2) - ((n : ℝ) + 1) / ((n : ℝ) + 3) * H y ^ (n + 3))) _ x := h3
    refine h4.congr_deriv ?_
    simp [gdens, h]
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp only [H_one, H_neg_one]
    push_cast
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    unfold gdens h
    have := cont_H
    fun_prop

theorem solution :
    (∀ z : ℕ, 1 ≤ z → X1 z = ((z : ℝ) - 1) / ((z : ℝ) + 1)) ∧
    (∀ z : ℕ, 2 ≤ z → X2 z = ((z : ℝ) - 3) / ((z : ℝ) + 1) ∧
      (1 / (z : ℝ)) * (X1 z - X2 z) = 2 / ((z : ℝ) * ((z : ℝ) + 1))) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, z = n + 1 := ⟨z - 1, by omega⟩
    exact X1_eq n
  · obtain ⟨n, rfl⟩ : ∃ n, z = n + 2 := ⟨z - 2, by omega⟩
    refine ⟨X2_eq n, ?_⟩
    have h1 := X1_eq (n + 1)
    have h2 := X2_eq n
    rw [show n + 1 + 1 = n + 2 from rfl] at h1
    rw [h1, h2]
    push_cast
    field_simp
    ring
