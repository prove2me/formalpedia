-- Prove2me | solution 1 for ShortTermDisclosure.Equilibrium.gap_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:07:15.522765+00:00
-- url     : https://prove2.me/submissions/22f4217e-423e-4a88-83a1-7dbb3af25861

import Mathlib
set_option autoImplicit false

theorem solution (ell muhi v1 v2 : ℝ)
    (hell0 : 0 < ell) (hell1 : ell < 1) (hm : v2 < muhi) :
    (ell * muhi + (1 - ell) / 2 * v1 - (1 + ell) / 2 * v2 = 0 ↔
      v1 = (1 + ell) / (1 - ell) * v2 - 2 * ell / (1 - ell) * muhi) ∧
    (ell * muhi + (1 - ell) / 2 * v1 - (1 + ell) / 2 * v2 = 0 →
      v2 - v1 = 2 * ell / (1 - ell) * (muhi - v2) ∧ 0 < v2 - v1) := by
  have h1 : 0 < 1 - ell := by linarith
  have h1' : (1 - ell) ≠ 0 := h1.ne'
  have key : v1 = (1 + ell) / (1 - ell) * v2 - 2 * ell / (1 - ell) * muhi ↔
      ell * muhi + (1 - ell) / 2 * v1 - (1 + ell) / 2 * v2 = 0 := by
    constructor
    · intro h
      have : (1 - ell) * v1 = (1 + ell) * v2 - 2 * ell * muhi := by
        rw [h]; field_simp
      linarith
    · intro h
      have : (1 - ell) * v1 = (1 + ell) * v2 - 2 * ell * muhi := by linarith
      field_simp
      linarith
  refine ⟨key.symm, ?_⟩
  intro h
  have hv := key.mpr h
  have e : v2 - v1 = 2 * ell / (1 - ell) * (muhi - v2) := by
    rw [hv]; field_simp; ring
  refine ⟨e, ?_⟩
  rw [e]
  have : 0 < muhi - v2 := by linarith
  positivity
