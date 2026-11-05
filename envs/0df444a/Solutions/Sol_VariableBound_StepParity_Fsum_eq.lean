-- Prove2me | solution 1 for VariableBound.StepParity.Fsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:49:00.734865+00:00
-- url     : https://prove2.me/submissions/c8ddb52c-a797-467c-a47b-8479eaad7481

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_StepParity
import Theorems.Thm_VariableBound_StepParity_eta_mul_allEven

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]
variable [Fintype X]
namespace VariableBound.StepParity
theorem _root_.solution {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) : Fsum V nb L = #{ξ | V ξ = ∅} := by
  rw [Fsum, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [eta_mul_allEven h]
  split_ifs <;> simp
end VariableBound.StepParity
