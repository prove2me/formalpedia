-- Prove2me | solution 1 for P2M_CircuitLowerBound_Tab_getElem__input_self_5981bb8d926a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:00.368846+00:00
-- url     : https://prove2.me/submissions/2da13054-37fb-45f7-a1be-b7d8aaf76de5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Complete
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool) [Finite (Case N)]
variable {N}
omit [Finite (Case N)]
namespace CircuitLowerBound.Tab
theorem _root_.solution (P : ℕ) (y : List Bool) :
    ((unary P ++ y).map N.inputAlphabet.invFun)[P]? = some (N.inputAlphabet.symm false) := by
  simp [unary]
end CircuitLowerBound.Tab
