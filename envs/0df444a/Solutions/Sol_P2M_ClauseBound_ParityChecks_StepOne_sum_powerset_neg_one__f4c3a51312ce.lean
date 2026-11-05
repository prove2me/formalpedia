-- Prove2me | solution 1 for P2M_ClauseBound_ParityChecks_StepOne_sum_powerset_neg_one__f4c3a51312ce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:08:15.131558+00:00
-- url     : https://prove2.me/submissions/0d5ef9b1-4fbd-4934-87c3-435c0fee0e4c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution {E : Type} [DecidableEq E] {A : Finset E} (hA : A ≠ ∅) : ∑ s ∈ A.powerset, (-1 : ℤ) ^ #s = 0 := by
  rw [sum_powerset_neg_one_pow_card, if_neg hA]
end ClauseBound.ParityChecks.StepOne
