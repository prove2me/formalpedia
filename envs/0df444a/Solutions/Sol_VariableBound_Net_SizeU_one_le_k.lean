-- Prove2me | solution 1 for VariableBound.Net.SizeU.one_le_k
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:30:19.051732+00:00
-- url     : https://prove2.me/submissions/f0ce6079-62c2-4073-a9cd-b2fb07ba65e0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}
namespace VariableBound.Net.SizeU
theorem _root_.solution (hW : WfD k n D) (hm : 0 < D.1.length) : 1 ≤ k := by
  obtain ⟨h1, h2, -⟩ := hW.1 D.1 (List.mem_singleton.2 rfl) D.1[0] (List.getElem_mem hm)
  exact (List.length_pos_iff.2 h1).trans_le h2
end VariableBound.Net.SizeU
