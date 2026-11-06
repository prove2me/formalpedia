-- Prove2me | solution 1 for StepSparsify.yC_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:46:46.861897+00:00
-- url     : https://prove2.me/submissions/fe33d69b-760f-4157-823a-90a9e175d35d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_CalNumbers
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Real
import Definitions.Def_SparsificationLemma_Cal_Facts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_StepSparsify_CalLeaves

set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify CountKSat SparsificationLemma
namespace StepSparsify
theorem _root_.solution {k K : ℕ} (α : ℕ) (hk : 1 ≤ k) (hK : k ≤ K) (hα : 1 ≤ α) : Cal.yC k α ≤ Cal.yC K α := by
  have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h2 : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h3 : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
  have h4 : 0 ≤ Real.logb 2 (32 * (α : ℝ)) := Real.logb_nonneg (by norm_num) (by linarith)
  have h5 : ((k : ℝ) - 1) ^ 2 ≤ ((K : ℝ) - 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  unfold Cal.yC
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (by norm_num)) h4) (by positivity)
end StepSparsify
