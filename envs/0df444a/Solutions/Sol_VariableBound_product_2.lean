-- Prove2me | solution 2 for VariableBound.product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:49:45.611373+00:00
-- url     : https://prove2.me/submissions/ec4b3860-f42c-4403-9d4d-66c6219974c7

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
import Theorems.Thm_VariableBound_StepParity_Fsum_eq

set_option autoImplicit false
section
section
open VariableBound
open Finset ParityChecks AppVariables StepParity
namespace VariableBound
theorem _root_.solution : AppVariables.ProductStmt := fun _ _ _ _ _ _ _ _ h => Fsum_eq h
end VariableBound
