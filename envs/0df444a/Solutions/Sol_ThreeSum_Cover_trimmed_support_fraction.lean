-- Prove2me | solution 1 for ThreeSum.Cover.trimmed_support_fraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:02.940075+00:00
-- url     : https://prove2.me/submissions/b7df6f0f-7d90-467c-ab84-3d04402e2685

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Cover
import Definitions.Def_WeightedCache3SUM_Alias_5b3840f7dbce14a8

set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
namespace ThreeSum.Cover
theorem _root_.solution {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (mu : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (hlower : 1 ≤ 16 * (mu + 1 : ℝ) * lam)
    (hfirst : lam * Fintype.card Ω / 2 ≤ ∑ ω, f ω)
    (hsecond : (∑ ω, (f ω) ^ 2) ≤ 5 * lam * Fintype.card Ω) :
    (Fintype.card Ω : ℝ) ≤
      320 * (mu + 1 : ℝ) * ((univ.filter fun ω => f ω ≠ 0).card : ℝ) := by
  classical
  have h := trimmed_support_lower f hlam hfirst hsecond
  have h₁ := mul_le_mul_of_nonneg_right hlower
    (show (0 : ℝ) ≤ Fintype.card Ω by positivity)
  have h₂ := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ 16 * (mu + 1 : ℝ) by positivity)
  nlinarith
end ThreeSum.Cover
