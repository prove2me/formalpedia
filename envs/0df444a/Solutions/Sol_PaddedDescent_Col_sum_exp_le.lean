-- Prove2me | solution 1 for PaddedDescent.Col.sum_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:02.867099+00:00
-- url     : https://prove2.me/submissions/2527fd7f-4ad3-4eae-b353-09eefedacd8f

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
import Theorems.Thm_PaddedDescent_Col_exp_le_quad

set_option autoImplicit false
section
section
open Finset
open PaddedDescent PaddedDescent.Col
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace PaddedDescent.Col
theorem _root_.solution (x : ι → ℝ) (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b ≤ 1) (γ : κ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∑ χ : ι → κ, Real.exp (θ * Wt x γ χ)
      ≤ (Fintype.card κ : ℝ) ^ Fintype.card ι * Real.exp ((θ + θ ^ 2) * ((∑ b, x b) / Fintype.card κ)) := by
  have hK : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos_iff.2 ⟨γ⟩
  have e1 : ∀ χ : ι → κ, Real.exp (θ * Wt x γ χ) = ∏ b, Real.exp (if χ b = γ then θ * x b else 0) := by
    intro χ
    rw [← Real.exp_sum, Wt, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have e2 : ∑ χ : ι → κ, ∏ b, Real.exp (if χ b = γ then θ * x b else 0)
      = ∏ b, ∑ k : κ, Real.exp (if k = γ then θ * x b else 0) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have e3 : ∀ b, ∑ k : κ, Real.exp (if k = γ then θ * x b else 0) = ((Fintype.card κ : ℝ) - 1) + Real.exp (θ * x b) := by
    intro b
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ γ)]
    have : ∀ k ∈ (univ : Finset κ).erase γ, Real.exp (if k = γ then θ * x b else 0) = 1 := by
      intro k hk
      rw [if_neg (Finset.ne_of_mem_erase hk), Real.exp_zero]
    rw [Finset.sum_congr rfl this, if_pos rfl, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ γ), Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.cast_sub (Fintype.card_pos_iff.2 ⟨γ⟩), Nat.cast_one]
    ring
  have e4 : ∀ b, ((Fintype.card κ : ℝ) - 1) + Real.exp (θ * x b)
      ≤ (Fintype.card κ : ℝ) * Real.exp ((θ + θ ^ 2) * (x b / Fintype.card κ)) := by
    intro b
    have hy0 : 0 ≤ θ * x b := mul_nonneg h0 (hx0 b)
    have hy1 : θ * x b ≤ 1 := by nlinarith [hx0 b, hx1 b]
    have q := exp_le_quad hy0 hy1
    have q2 : (θ * x b) ^ 2 ≤ θ ^ 2 * x b := by
      have : x b ^ 2 ≤ x b := by nlinarith [hx0 b, hx1 b]
      calc (θ * x b) ^ 2 = θ ^ 2 * x b ^ 2 := by ring
        _ ≤ θ ^ 2 * x b := by gcongr
    have q3 := Real.add_one_le_exp ((θ + θ ^ 2) * (x b / Fintype.card κ))
    calc ((Fintype.card κ : ℝ) - 1) + Real.exp (θ * x b) ≤ (Fintype.card κ : ℝ) + (θ + θ ^ 2) * x b := by nlinarith
      _ = (Fintype.card κ : ℝ) * ((θ + θ ^ 2) * (x b / Fintype.card κ) + 1) := by field_simp; ring
      _ ≤ _ := by gcongr
  simp_rw [e1]
  rw [e2]
  simp_rw [e3]
  calc ∏ b, (((Fintype.card κ : ℝ) - 1) + Real.exp (θ * x b))
      ≤ ∏ b, ((Fintype.card κ : ℝ) * Real.exp ((θ + θ ^ 2) * (x b / Fintype.card κ))) := by
        refine Finset.prod_le_prod (fun b _ => ?_) fun b _ => e4 b
        have : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos_iff.2 ⟨γ⟩
        have := Real.exp_pos (θ * x b)
        linarith
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum, ← Finset.mul_sum, Finset.sum_div]
end PaddedDescent.Col
