-- Prove2me | solution 1 for VariableBound.StepParity.allEven_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:46:49.318198+00:00
-- url     : https://prove2.me/submissions/597e9f2b-0be5-40c9-b360-d8ce419c26c6

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
import Theorems.Thm_VariableBound_StepParity_term_nonneg

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]
variable [Fintype X]
namespace VariableBound.StepParity
theorem _root_.solution {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) {ξ : X} (hξ : nb < #(V ξ)) : allEven V L ξ = 0 := by
  have h1 := (sum_eq_zero_iff_of_nonneg fun ξ _ => term_nonneg V nb L ξ).1 h ξ (mem_univ ξ)
  have h2 : ((#(V ξ)).choose (nb + 1) : ℤ) ≠ 0 := Int.natCast_ne_zero.2 (Nat.choose_pos hξ).ne'
  exact (mul_eq_zero.1 h1).resolve_left h2
end VariableBound.StepParity
