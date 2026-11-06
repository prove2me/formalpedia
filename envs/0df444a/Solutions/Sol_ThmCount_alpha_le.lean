-- Prove2me | solution 1 for ThmCount.alpha_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:59:31.037704+00:00
-- url     : https://prove2.me/submissions/7ac04b37-5079-485c-a4e1-061ab00e7688

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
import Theorems.Thm_Sat3_one_le_logb
import Theorems.Thm_SparsificationLemma_Cal_stLogC
import Theorems.Thm_ThmCount_one_le_logb


set_option autoImplicit false
section
section
open ThmCount
open PaperSentences
namespace ThmCount
theorem _root_.solution {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : (SparsificationLemma.Cal.alphaC 3 ε : ℝ) ≤ 73 * (Real.logb 2 (1 / (ε : ℝ)) / (ε : ℝ)) := by
  have e0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have e1 : (ε : ℝ) ≤ 1 / 2 := by
    have := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at this
    exact this
  obtain ⟨lam, hlam⟩ : ∃ l, l = Real.logb 2 (1 / (ε : ℝ)) := ⟨_, rfl⟩
  rw [← hlam]
  have hl1 : 1 ≤ lam := by
    rw [hlam]
    refine one_le_logb ?_
    rw [le_div_iff₀ e0]
    linarith
  have hx : ((SparsificationLemma.Cal.xC 3 ε : ℚ) : ℝ) = 128 * (1 / (ε : ℝ)) := by
    unfold SparsificationLemma.Cal.xC
    push_cast
    ring
  have h128 : Real.logb 2 (128 : ℝ) = 7 := by
    rw [show (128 : ℝ) = (2 : ℝ) ^ (7 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    norm_num
  have hlog : Real.logb 2 ((SparsificationLemma.Cal.xC 3 ε : ℚ) : ℝ) = 7 + lam := by
    rw [hx, Real.logb_mul (by norm_num) (by positivity), ← hlam, h128]
  have hL : (SparsificationLemma.Cal.logC 3 ε : ℝ) ≤ 8 + lam := by
    have h := SparsificationLemma.Cal.stLogC 3 ε (by norm_num) h0 (by linarith)
    have h2 := Int.ceil_lt_add_one (Real.logb 2 ((SparsificationLemma.Cal.xC 3 ε : ℚ) : ℝ))
    rw [← h, hlog] at h2
    push_cast at h2
    linarith
  have hA : (SparsificationLemma.Cal.alphaC 3 ε : ℝ) ≤ 8 / (ε : ℝ) * (SparsificationLemma.Cal.logC 3 ε : ℝ) + 1 := by
    have hnn : (0 : ℚ) ≤ 2 * (((3 : ℕ) : ℚ) - 1) ^ 2 / ε * (SparsificationLemma.Cal.logC 3 ε : ℚ) := by positivity
    have h : ((SparsificationLemma.Cal.alphaC 3 ε : ℕ) : ℚ) < 2 * (((3 : ℕ) : ℚ) - 1) ^ 2 / ε * (SparsificationLemma.Cal.logC 3 ε : ℚ) + 1 := Nat.ceil_lt_add_one hnn
    have h' := (Rat.cast_le (K := ℝ)).2 h.le
    push_cast at h'
    have e : 2 * ((3 : ℝ) - 1) ^ 2 / (ε : ℝ) * (SparsificationLemma.Cal.logC 3 ε : ℝ) + 1 = 8 / (ε : ℝ) * (SparsificationLemma.Cal.logC 3 ε : ℝ) + 1 := by ring
    rw [e] at h'
    exact h'
  have h8 : (0 : ℝ) ≤ 8 / (ε : ℝ) := by positivity
  have hle : 1 ≤ lam / (ε : ℝ) := by
    rw [le_div_iff₀ e0]
    linarith
  have u1 : 8 / (ε : ℝ) * (SparsificationLemma.Cal.logC 3 ε : ℝ) ≤ 8 / (ε : ℝ) * (9 * lam) := mul_le_mul_of_nonneg_left (by linarith) h8
  have u2 : 8 / (ε : ℝ) * (9 * lam) + lam / (ε : ℝ) = 73 * (lam / (ε : ℝ)) := by ring
  linarith
end ThmCount
