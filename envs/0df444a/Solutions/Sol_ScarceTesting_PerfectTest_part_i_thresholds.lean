-- Prove2me | solution 1 for ScarceTesting.PerfectTest.part_i_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:57:41.118028+00:00
-- url     : https://prove2.me/submissions/26bde77e-c6fe-4691-832a-31460e953e51

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

set_option autoImplicit false
open MeasureTheory Set ScarceTesting.PerfectTest

theorem solution (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∀ φ : ℝ, φ < 1 → tH c φ 1 = 1) ∧
    (∀ φ : ℝ, tL c φ 1 = c * φ / (c * φ + (1 - c))) ∧
    HasDerivAt (fun φ => tL c φ 1) (c / (1 - c)) 0 := by
  have h1c : 0 < 1 - c := by linarith
  have hL : (fun φ : ℝ => tL c φ 1) = fun φ => c * φ / (c * φ + (1 - c)) := by
    funext φ; simp [tL]
  refine ⟨?_, fun φ => by simp [tL], ?_⟩
  · intro φ hφ
    have : 0 < 1 - φ := by linarith
    unfold tH
    have h : c * (1 - φ) ≠ 0 := by positivity
    simp [h]
  · rw [hL]
    have h1 : HasDerivAt (fun φ : ℝ => c * φ) c 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_mul c
    have h2 : HasDerivAt (fun φ : ℝ => c * φ + (1 - c)) c 0 := h1.add_const _
    have := h1.div h2 (by simp; linarith)
    refine HasDerivAt.congr_deriv this ?_
    have e : c * 0 + (1 - c) = 1 - c := by ring
    rw [e]
    have hc : (1 - c) ≠ 0 := h1c.ne'
    field_simp
    ring
