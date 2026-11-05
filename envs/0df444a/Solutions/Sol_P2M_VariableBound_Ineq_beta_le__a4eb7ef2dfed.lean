-- Prove2me | solution 1 for P2M_VariableBound_Ineq_beta_le__a4eb7ef2dfed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:55:40.978201+00:00
-- url     : https://prove2.me/submissions/a5b4222f-2471-4128-88b5-d20e8d69c84a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
import Theorems.Thm_VariableBound_Ineq_nb_mul_le

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {n Δ nb : ℕ} (hΔ : 1 ≤ Δ) (h : IsNb n Δ nb) : (n : ℝ) + 3 * (nb + 1) * lg (2 * Δ) + 2 ≤ 4 * n + 3 * lg (2 * Δ) + 2 := by
  have h1 := nb_mul_le hΔ h
  linarith
end VariableBound.Ineq
