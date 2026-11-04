-- Prove2me | solution 1 for ThreeSum.Cover.trimmed_support_lower_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:08.238945+00:00
-- url     : https://prove2.me/submissions/b16dfac7-81d5-4c43-9bf2-2518ddcc8de1

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
import Definitions.Def_WeightedCache3SUM_Alias_20e0db851a3633f6

set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
namespace ThreeSum.Cover
theorem _root_.solution {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hfirst : lam * Fintype.card Ω / 2 ≤ ∑ ω, f ω)
    (hsecond : (∑ ω, (f ω) ^ 2) ≤ 5 * lam * Fintype.card Ω) :
    lam * Fintype.card Ω ≤
      20 * ((univ.filter fun ω => f ω ≠ 0).card : ℝ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hL : 0 < lam * Fintype.card Ω := mul_pos hlam hN
  have hc : (0 : ℝ) ≤ (univ.filter fun ω => f ω ≠ 0).card := by positivity
  have hS : 0 ≤ ∑ ω, f ω := le_trans (by positivity) hfirst
  have hsq := support_cauchy f
  have hup := mul_le_mul_of_nonneg_left hsecond hc
  have hlo : (lam * Fintype.card Ω) ^ 2 ≤ 4 * (∑ ω, f ω) ^ 2 := by
    nlinarith
  nlinarith
end ThreeSum.Cover
