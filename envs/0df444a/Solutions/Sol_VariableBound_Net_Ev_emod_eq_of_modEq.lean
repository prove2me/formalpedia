-- Prove2me | solution 1 for VariableBound.Net.Ev.emod_eq_of_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:36:33.107+00:00
-- url     : https://prove2.me/submissions/e91c9a31-9ad0-427e-9cbe-e8130fc36ec9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_Ev

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Ev
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg
open ClauseBound.ParityChecks (Vof)
namespace VariableBound.Net.Ev
theorem _root_.solution {a b N : ℤ} (h : a ≡ b [ZMOD N]) (h0 : 0 ≤ a) (h1 : a < N) : b % N = a := by
  rw [← h.eq]; exact Int.emod_eq_of_lt h0 h1
end VariableBound.Net.Ev
