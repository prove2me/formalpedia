-- Prove2me | solution 1 for VariableBound.Net.FitL.clog_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:35:47.778197+00:00
-- url     : https://prove2.me/submissions/f5dbfe55-387a-4014-88fc-29b977d637ff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_VariableBound_Net_Fit
import Theorems.Thm_VariableBound_Net_FitL_two_mul_le
import Theorems.Thm_VariableBound_Net_FitL_two_le_LD
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_LD


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
theorem _root_.solution {Δ : ℕ} (hΔ : 2 ≤ Δ) : Nat.clog 2 (96 * Δ * LD Δ) ≤ 2 * LD Δ + 5 := by
  refine Nat.clog_le_of_le_pow ?_
  have h1 := two_mul_le Δ
  have hL := two_le_LD hΔ
  generalize LD Δ = L at h1 hL ⊢
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have h2 : Δ ≤ 2 ^ L' := by rw [pow_succ] at h1; omega
  have h3 : L' + 1 ≤ 2 ^ L' := Nat.lt_two_pow_self
  calc 96 * Δ * (L' + 1) ≤ 128 * 2 ^ L' * 2 ^ L' := Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) h2) h3
    _ = 2 ^ (2 * (L' + 1) + 5) := by ring
end VariableBound.Net.FitL
