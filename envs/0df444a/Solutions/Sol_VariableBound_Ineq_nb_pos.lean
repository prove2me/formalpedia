-- Prove2me | solution 1 for VariableBound.Ineq.nb_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:50:53.94439+00:00
-- url     : https://prove2.me/submissions/93133975-65bf-4de2-88db-61fe3832819c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {n Δ nb : ℕ} (h : IsNb n Δ nb) : (1 : ℝ) ≤ nb := by
  obtain ⟨a, rfl⟩ := h.1
  exact_mod_cast Nat.one_le_two_pow
end VariableBound.Ineq
