-- Prove2me | solution 1 for VariableBound.StepParity.allEven_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:45:41.037202+00:00
-- url     : https://prove2.me/submissions/3fb20aaf-8eca-40c0-b6b4-cfecac5812a7

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
import Theorems.Thm_VariableBound_StepParity_allEven_eq_fin
import Theorems.Thm_VariableBound_StepParity_ev_nonneg
import Theorems.Thm_VariableBound_StepParity_ev_le_one

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]
namespace VariableBound.StepParity
theorem _root_.solution (V : X → Finset E) (L : List (Finset E)) (ξ : X) : allEven V L ξ ≤ 1 := by
  rw [allEven_eq_fin]
  exact prod_le_one (fun j _ => ev_nonneg _) fun j _ => ev_le_one _
end VariableBound.StepParity
