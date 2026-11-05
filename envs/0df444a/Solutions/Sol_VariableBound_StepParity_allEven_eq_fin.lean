-- Prove2me | solution 1 for VariableBound.StepParity.allEven_eq_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:36.788813+00:00
-- url     : https://prove2.me/submissions/c609ff1a-28df-4311-8440-36afca6e04eb

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

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]
namespace VariableBound.StepParity
theorem _root_.solution (V : X → Finset E) (L : List (Finset E)) (ξ : X) : allEven V L ξ = ∏ j : Fin L.length, ev #(L.getD j ∅ ∩ V ξ) := by
  rw [allEven, ← Fin.prod_univ_fun_getElem]
  exact prod_congr rfl fun j _ => by rw [List.getD_eq_getElem _ _ j.isLt]
end VariableBound.StepParity
