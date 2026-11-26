-- Prove2me | solution 1 for Sendov.integral_moment_rec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:25.588295+00:00
-- url     : https://prove2.me/submissions/8d5129bf-d656-4e36-95e0-b85835695c61

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_qrow
import Theorems.Thm_Sendov_integral_irow
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.rev_cons

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {n k : ℕ} {α D : ℝ} {g₀ g₁ g₂ : List ℤ} (hD : D ≠ 0)
    (hQ : ∀ t : ℝ, D * Q n α t = pev g₀ α + pev g₁ α * t + pev g₂ α * t ^ 2) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k) = irow (qrow g₀ g₁ g₂ k) 0 α / D ^ k := by
  have hpow : ∀ t : ℝ, t ^ 3 * Q n α t ^ k
      = (t ^ (0 + 3) * rev (qrow g₀ g₁ g₂ k) α t) / D ^ k := by
    intro t
    rw [rev_qrow, ← hQ t, mul_pow]
    field_simp
    ring
  simp only [hpow]
  rw [intervalIntegral.integral_div, integral_irow]
end Sendov
