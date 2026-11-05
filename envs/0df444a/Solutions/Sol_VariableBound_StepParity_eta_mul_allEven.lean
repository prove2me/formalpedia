-- Prove2me | solution 1 for VariableBound.StepParity.eta_mul_allEven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:48:23.172081+00:00
-- url     : https://prove2.me/submissions/3789fcd7-a776-4539-a161-c0b678febc60

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
import Theorems.Thm_VariableBound_StepParity_allEven_eq_range
import Theorems.Thm_VariableBound_StepParity_good_of_Xsum_eq_zero
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_product


set_option autoImplicit false
section
section
open VariableBound VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]
variable [Fintype X]
namespace VariableBound.StepParity
theorem _root_.solution {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) (ξ : X) :
    eta V nb ξ * allEven V L ξ = if V ξ = ∅ then 1 else 0 := by
  rw [allEven_eq_range]
  exact ClauseBound.ParityChecks.StepOne.product V nb L.length (fun j => L.getD j ∅) (good_of_Xsum_eq_zero h) ξ
end VariableBound.StepParity
