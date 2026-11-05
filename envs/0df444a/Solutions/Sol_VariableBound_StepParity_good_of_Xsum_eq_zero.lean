-- Prove2me | solution 1 for VariableBound.StepParity.good_of_Xsum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:47:40.047772+00:00
-- url     : https://prove2.me/submissions/6e0be6dc-933e-4976-bac8-62d0e7604ac9

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
import Theorems.Thm_VariableBound_StepParity_allEven_eq_zero

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]
variable [Fintype X]
namespace VariableBound.StepParity
theorem _root_.solution {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) (ξ : X) (hξ : nb < #(V ξ)) :
    ∃ j < L.length, Odd #(L.getD j ∅ ∩ V ξ) := by
  have h1 := allEven_eq_zero h hξ
  rw [allEven_eq_range, prod_eq_zero_iff] at h1
  obtain ⟨j, hj, h2⟩ := h1
  refine ⟨j, mem_range.1 hj, Nat.not_even_iff_odd.1 fun he => ?_⟩
  rw [ev, if_pos he] at h2
  exact one_ne_zero h2
end VariableBound.StepParity
