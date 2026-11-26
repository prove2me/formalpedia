-- Prove2me | solution 1 for Sendov.integral_irow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:11:01.114648+00:00
-- url     : https://prove2.me/submissions/b7f0a787-085a-4d78-b49b-a49a0533759f

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_continuous_rev
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.rev_cons

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (r : List (List ℤ)) (i : ℕ) (α : ℝ) :
    (∫ t in (0 : ℝ)..1, t ^ (i + 3) * rev r α t) = irow r i α := by
  induction r generalizing i with
  | nil => simp [irow]
  | cons p r ih =>
    have hfun : (fun t : ℝ => t ^ (i + 3) * rev (p :: r) α t)
        = fun t : ℝ => pev p α * t ^ (i + 3) + t ^ (i + 1 + 3) * rev r α t := by
      funext t
      simp only [rev_cons]
      ring
    have h1 : IntervalIntegrable (fun t : ℝ => pev p α * t ^ (i + 3)) volume 0 1 :=
      (by fun_prop : Continuous fun t : ℝ => pev p α * t ^ (i + 3)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t : ℝ => t ^ (i + 1 + 3) * rev r α t) volume 0 1 :=
      ((continuous_pow _).mul (continuous_rev r α)).intervalIntegrable _ _
    rw [hfun, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      integral_pow, ih]
    simp only [irow]
    push_cast
    ring
end Sendov
