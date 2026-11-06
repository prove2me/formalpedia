-- Prove2me | solution 1 for ThmCount.deg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:09:00.744936+00:00
-- url     : https://prove2.me/submissions/fda62aea-676a-4b7e-93a3-e6a16cf10aad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_Rates
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_StepSparsify
import Definitions.Def_SparsificationLemma_Sketch
import Mathlib.Tactic
import Definitions.Def_ThmCount_MEps
import Theorems.Thm_ThmCount_alpha_le
import Theorems.Thm_ThmCount_sq_eq
import Theorems.Thm_Sat3_one_le_logb
import Theorems.Thm_ThmCount_one_le_logb


set_option autoImplicit false
section
section
open ThmCount
open PaperSentences
namespace ThmCount
theorem _root_.solution {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    ((2 + 4 * SparsificationLemma.Cal.alphaC 3 ε * (32 * SparsificationLemma.Cal.alphaC 3 ε) : ℕ) : ℝ) ≤ 682114 * ((ε : ℝ) ^ (-2 : ℝ) * lg (1 / (ε : ℝ)) ^ 2) := by
  have e0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have e1 : (ε : ℝ) ≤ 1 / 2 := by
    have := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at this
    exact this
  have hα := alpha_le h0 h1
  have hl1 : 1 ≤ Real.logb 2 (1 / (ε : ℝ)) := by
    refine one_le_logb ?_
    rw [le_div_iff₀ e0]
    linarith
  unfold lg
  rw [sq_eq e0]
  obtain ⟨t, ht⟩ : ∃ t, t = Real.logb 2 (1 / (ε : ℝ)) / (ε : ℝ) := ⟨_, rfl⟩
  rw [← ht] at hα ⊢
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ e0]
    linarith
  have hα0 : (0 : ℝ) ≤ (SparsificationLemma.Cal.alphaC 3 ε : ℝ) := Nat.cast_nonneg _
  have hsq : (SparsificationLemma.Cal.alphaC 3 ε : ℝ) ^ 2 ≤ (73 * t) ^ 2 := pow_le_pow_left₀ hα0 hα 2
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
  push_cast
  nlinarith
end ThmCount
