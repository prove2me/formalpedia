-- Prove2me | solution 1 for VariableBound.Count.row_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:37:13.619328+00:00
-- url     : https://prove2.me/submissions/d02ddde1-c01c-4a5e-8aaa-8360e90b5e08

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
import Theorems.Thm_VariableBound_Count_lg_le_LD

set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
namespace VariableBound.Count
theorem _root_.solution (hIneq : ParamIneq) (n Δ m nb c : ℕ) (hΔ : 2 ≤ Δ) (hm : m ≤ Δ * n) (hNb : IsNb n Δ nb) (h : nb * c ≤ 16 * m) : c ≤ sbMax Δ := by
  have h1 := (hIneq.sb_lt n Δ m nb hΔ hm hNb).2
  have h2 := lg_le_LD Δ (by omega)
  have h0 : (0 : ℝ) < nb := by
    obtain ⟨a, rfl⟩ := hNb.1
    positivity
  have h3 : (nb : ℝ) * c ≤ 16 * m := by exact_mod_cast h
  have h4 : (c : ℝ) ≤ 16 * m / nb := by rw [le_div_iff₀ h0]; linarith
  have h5 : (32 : ℝ) * Δ * lg (2 * Δ) ≤ 32 * Δ * LD Δ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h6 : (c : ℝ) ≤ (sbMax Δ : ℕ) := by unfold sbMax; push_cast; linarith
  exact_mod_cast h6
end VariableBound.Count
