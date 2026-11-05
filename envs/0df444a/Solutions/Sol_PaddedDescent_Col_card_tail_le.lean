-- Prove2me | solution 1 for PaddedDescent.Col.card_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:42.080654+00:00
-- url     : https://prove2.me/submissions/53e8a9e9-8889-498c-9fa3-b994ba4c86f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Definitions.Def_PaddedDescent_Col_Colouring
import Theorems.Thm_PaddedDescent_Col_sum_exp_le

set_option autoImplicit false
section
section
open Finset
open PaddedDescent PaddedDescent.Col
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace PaddedDescent.Col
theorem _root_.solution (x : ι → ℝ) (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b ≤ 1) (γ : κ) {δ s : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hs : (∑ b, x b) / Fintype.card κ ≤ s) :
    (#{χ : ι → κ | (∑ b, x b) / Fintype.card κ + δ * s ≤ Wt x γ χ} : ℝ)
      ≤ (Fintype.card κ : ℝ) ^ Fintype.card ι * Real.exp (-(δ ^ 2 * s / 4)) := by
  set μ : ℝ := (∑ b, x b) / Fintype.card κ with hμ
  have hθ0 : (0 : ℝ) ≤ δ / 2 := by linarith
  have hθ1 : δ / 2 ≤ 1 := by linarith
  have h := sum_exp_le x hx0 hx1 γ hθ0 hθ1
  have m : (#{χ : ι → κ | μ + δ * s ≤ Wt x γ χ} : ℝ) * Real.exp (δ / 2 * (μ + δ * s)) ≤ ∑ χ : ι → κ, Real.exp (δ / 2 * Wt x γ χ) := by
    calc (#{χ : ι → κ | μ + δ * s ≤ Wt x γ χ} : ℝ) * Real.exp (δ / 2 * (μ + δ * s))
        = ∑ χ ∈ ({χ : ι → κ | μ + δ * s ≤ Wt x γ χ} : Finset (ι → κ)), Real.exp (δ / 2 * (μ + δ * s)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ χ ∈ ({χ : ι → κ | μ + δ * s ≤ Wt x γ χ} : Finset (ι → κ)), Real.exp (δ / 2 * Wt x γ χ) := by
          refine Finset.sum_le_sum fun χ hχ => Real.exp_le_exp.2 ?_
          exact mul_le_mul_of_nonneg_left (Finset.mem_filter.1 hχ).2 hθ0
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => (Real.exp_pos _).le
  have hpos := Real.exp_pos (δ / 2 * (μ + δ * s))
  have key : (#{χ : ι → κ | μ + δ * s ≤ Wt x γ χ} : ℝ)
      ≤ (Fintype.card κ : ℝ) ^ Fintype.card ι * (Real.exp ((δ / 2 + (δ / 2) ^ 2) * μ) * Real.exp (-(δ / 2 * (μ + δ * s)))) := by
    rw [Real.exp_neg, ← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact m.trans h
  refine key.trans ?_
  rw [← Real.exp_add]
  gcongr
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (δ / 2))]
end PaddedDescent.Col
