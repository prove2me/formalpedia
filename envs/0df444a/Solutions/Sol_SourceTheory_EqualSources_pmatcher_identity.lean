-- Prove2me | solution 1 for SourceTheory.EqualSources.pmatcher_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:28:44.45445+00:00
-- url     : https://prove2.me/submissions/dae18066-50b7-4feb-ab7a-f2f509b9feb3

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

set_option autoImplicit false
open Set

theorem solution (φ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ) (c : ℝ)
    (hlin : ∀ p ∈ Icc (0 : ℝ) (1 / 2), φ p = c * p) (hhalf : φ (1 / 2) = 1 / 2)
    (hsym : ∀ p ∈ Icc (0 : ℝ) 1, φ p + φ (1 - p) = 1) :
    ∀ p ∈ Icc (0 : ℝ) 1, φ p = p := by
  have hc : c = 1 := by
    have := hlin (1 / 2) ⟨by norm_num, le_rfl⟩
    rw [hhalf] at this
    linarith
  subst hc
  intro p hp
  by_cases h : p ≤ 1 / 2
  · rw [hlin p ⟨hp.1, h⟩]; ring
  · push_neg at h
    have h1 := hsym p hp
    have h2 := hlin (1 - p) ⟨by linarith [hp.2], by linarith⟩
    rw [h2] at h1
    linarith
