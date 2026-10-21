-- Prove2me | solution 1 for ScarceTesting.PerfectTest.part_ii_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:57:42.176494+00:00
-- url     : https://prove2.me/submissions/cbfaa355-a39a-423d-9c79-50c35459ae5d

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

set_option autoImplicit false
open MeasureTheory Set ScarceTesting.PerfectTest

theorem solution (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∀ σ : ℝ, tL c 0 σ = 0) ∧
    (∀ σ : ℝ, tH c 0 σ = c / (1 - (1 - c) * σ)) ∧
    HasDerivAt (fun σ => tH c 0 σ) ((1 - c) / c) 1 := by
  have h1c : 0 < 1 - c := by linarith
  have hH : (fun σ : ℝ => tH c 0 σ) = fun σ => c / (1 - (1 - c) * σ) := by
    funext σ; simp only [tH]; congr 1 <;> ring
  refine ⟨fun σ => by simp [tL], fun σ => by simp only [tH]; congr 1 <;> ring, ?_⟩
  rw [hH]
  have h1 : HasDerivAt (fun σ : ℝ => 1 - (1 - c) * σ) (-(1 - c)) 1 := by
    have := ((hasDerivAt_id (1:ℝ)).const_mul (1 - c)).const_sub 1
    simpa using this
  have := (hasDerivAt_const (1:ℝ) c).div h1 (by simp; exact hc0.ne')
  refine HasDerivAt.congr_deriv this ?_
  have e : 1 - (1 - c) * 1 = c := by ring
  rw [e]
  have hc : c ≠ 0 := hc0.ne'
  field_simp
  ring
