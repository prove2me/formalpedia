-- Prove2me | solution 1 for SplitSat.final_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:15:12.07197+00:00
-- url     : https://prove2.me/submissions/68fa9f0a-ad49-417a-ace3-ba146ff6d0ed

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes

set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify
namespace SplitSat
theorem _root_.solution (P₂ P₀ R c e W : ℕ) (h1 : 1 ≤ W) :
    P₂ * W ^ e + c * (R * W) ^ c + 4 ≤ cOf P₂ P₀ R c e * W ^ cOf P₂ P₀ R c e ∧ P₀ * W ^ e + 3 ≤ cOf P₂ P₀ R c e * W ^ cOf P₂ P₀ R c e := by
  have ee : W ^ e ≤ W ^ cOf P₂ P₀ R c e := Nat.pow_le_pow_right h1 (by unfold cOf; omega)
  have ec : W ^ c ≤ W ^ cOf P₂ P₀ R c e := Nat.pow_le_pow_right h1 (by unfold cOf; omega)
  have e0 : 1 ≤ W ^ cOf P₂ P₀ R c e := Nat.one_le_pow _ _ h1
  generalize W ^ cOf P₂ P₀ R c e = P at ee ec e0
  have hc : cOf P₂ P₀ R c e * P = P₂ * P + P₀ * P + c * R ^ c * P + c * P + e * P + 20 * P := by
    unfold cOf; ring
  have h3 : P₂ * W ^ e ≤ P₂ * P := Nat.mul_le_mul_left _ ee
  have h2 : P₀ * W ^ e ≤ P₀ * P := Nat.mul_le_mul_left _ ee
  have hA : c * (R * W) ^ c ≤ c * R ^ c * P := by
    rw [mul_pow, ← mul_assoc]
    exact Nat.mul_le_mul_left _ ec
  rw [hc]
  constructor <;> omega
end SplitSat
