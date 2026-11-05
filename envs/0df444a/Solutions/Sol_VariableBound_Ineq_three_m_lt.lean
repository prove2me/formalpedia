-- Prove2me | solution 1 for VariableBound.Ineq.three_m_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:57:14.136114+00:00
-- url     : https://prove2.me/submissions/1c269193-2bf3-4ecd-bd54-8a41811c14f7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
import Theorems.Thm_VariableBound_Ineq_nb_pos
import Theorems.Thm_VariableBound_Ineq_m_div_lt

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {n Δ m nb : ℕ} (hΔ : 2 ≤ Δ) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) : 3 * (m : ℝ) / (nb + 1) < 6 * Δ * lg (2 * Δ) := by
  have hnb := nb_pos h
  have h1 := m_div_lt hΔ hm h
  have h2 : (m : ℝ) / (nb + 1) ≤ m / nb := div_le_div_of_nonneg_left (Nat.cast_nonneg m) (by linarith) (by linarith)
  rw [mul_div_assoc]
  linarith
end VariableBound.Ineq
