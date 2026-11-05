-- Prove2me | solution 1 for VariableBound.StepParity.term_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:45:45.256078+00:00
-- url     : https://prove2.me/submissions/52f67e80-1d2f-4490-8093-c38d99f2253b

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
import Theorems.Thm_VariableBound_StepParity_allEven_nonneg

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]
namespace VariableBound.StepParity
theorem _root_.solution (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) (ξ : X) : 0 ≤ ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ :=
  mul_nonneg (Int.natCast_nonneg _) (allEven_nonneg V L ξ)
end VariableBound.StepParity
