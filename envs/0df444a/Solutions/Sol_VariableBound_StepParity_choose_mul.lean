-- Prove2me | solution 1 for VariableBound.StepParity.choose_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:45:10.266059+00:00
-- url     : https://prove2.me/submissions/eb2d7d44-6310-40d1-8d10-582944d8038d

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
theorem _root_.solution {E : Type} (A : Finset E) (c : ℕ) (y : ℤ) : ((#A).choose c : ℤ) * y = ∑ _S₀ ∈ A.powerset with #_S₀ = c, y := by
  rw [sum_const, ← powersetCard_eq_filter, card_powersetCard, nsmul_eq_mul]
end VariableBound.StepParity
