-- Prove2me | solution 1 for PaddedDescent.Col.mean_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:57:14.781936+00:00
-- url     : https://prove2.me/submissions/aeb51328-30cf-4f2a-a933-08b5e0e04cf8

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

set_option autoImplicit false
section
section
open Finset
open PaddedDescent PaddedDescent.Col
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]
namespace PaddedDescent.Col
theorem _root_.solution (x : ι → ℝ) (hx1 : ∀ b, x b ≤ 1) [Nonempty κ] :
    (∑ b, x b) / (Fintype.card κ : ℝ) ≤ (Fintype.card ι : ℝ) / Fintype.card κ := by
  have hK : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  gcongr
  calc ∑ b, x b ≤ ∑ _b : ι, (1 : ℝ) := Finset.sum_le_sum fun b _ => hx1 b
    _ = Fintype.card ι := by simp
end PaddedDescent.Col
