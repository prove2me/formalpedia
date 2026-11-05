-- Prove2me | solution 1 for Sat3.InTimeTM.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:22:29.068189+00:00
-- url     : https://prove2.me/submissions/82abcb1c-7ccb-41ca-97f7-ede9e3572582

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_ToTuring_EndLemmas
import Theorems.Thm_Sat3_DecidesTM_mono

set_option autoImplicit false
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
namespace InTimeTM
theorem _root_.solution {δ δ' : ℝ≥0} (h : InTimeTM δ) (hδ : δ ≤ δ') : InTimeTM δ' := by
  obtain ⟨M, c, hfin, hM⟩ := h
  refine ⟨M, c, hfin, hM.mono fun n => Nat.floor_le_floor ?_⟩
  have : (2 : ℝ) ^ ((δ : ℝ) * n) ≤ (2 : ℝ) ^ ((δ' : ℝ) * n) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n))
  exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg c)
end InTimeTM
end Sat3
