-- Prove2me | solution 1 for Sendov.rev_qrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:11:34.993771+00:00
-- url     : https://prove2.me/submissions/94d7027b-45d7-4d06-9ea1-72540a2cb503

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_radd
import Theorems.Thm_Sendov_rev_rscale
import Theorems.Thm_Sendov_rev_shift
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.rev_cons

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (g₀ g₁ g₂ : List ℤ) (k : ℕ) (α t : ℝ) :
    rev (qrow g₀ g₁ g₂ k) α t = (pev g₀ α + pev g₁ α * t + pev g₂ α * t ^ 2) ^ k := by
  induction k with
  | zero => simp [qrow]
  | succ k ih =>
    simp only [qrow, qstep, rev_radd, rev_rscale, rev_shift, ih, pow_succ]
    ring
end Sendov
