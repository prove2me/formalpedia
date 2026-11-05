-- Prove2me | solution 1 for VariableBound.Ineq.lt_nb_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:54:44.215086+00:00
-- url     : https://prove2.me/submissions/959ac06e-7605-4ec5-ba08-f5922f457704

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
theorem _root_.solution {n Δ nb : ℕ} (h : IsNb n Δ nb) : (n : ℝ) < 2 * nb * lg (2 * Δ) := by
  have h1 : (2 : ℝ) ^ n < ((2 : ℝ) * Δ) ^ (2 * nb) := by exact_mod_cast h.2.2
  have h2 := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h1
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  push_cast at h2
  exact h2
end VariableBound.Ineq
