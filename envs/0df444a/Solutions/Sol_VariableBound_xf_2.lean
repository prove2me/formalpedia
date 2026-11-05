-- Prove2me | solution 2 for VariableBound.xf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:47:41.052966+00:00
-- url     : https://prove2.me/submissions/c173ec74-39a7-4631-a0a2-a14264dfc109

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
import Theorems.Thm_VariableBound_StepParity_choose_mul
import Theorems.Thm_VariableBound_lemCutoff

set_option autoImplicit false
section
section
open VariableBound
open Finset ParityChecks AppVariables StepParity
namespace VariableBound
theorem _root_.solution : AppVariables.XFStmt := by
  intro X E _ _ _ V nb L β n M hβ hM hn
  constructor
  · simp only [← choose_mul]
    exact lemCutoff X E V L (fun ξ => ((#(V ξ)).choose (nb + 1) : ℤ)) β M hβ hM
  · simp only [← sum_mul]
    exact lemCutoff X E V L (eta V nb) (n + 1) M (Nat.succ_pos n) hn
end VariableBound
