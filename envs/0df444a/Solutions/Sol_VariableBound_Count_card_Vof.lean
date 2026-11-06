-- Prove2me | solution 1 for VariableBound.Count.card_Vof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:21.965674+00:00
-- url     : https://prove2.me/submissions/35e955d3-a110-4953-96bd-8a32ff88edc8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
import Theorems.Thm_VariableBound_Count_Vof_eq_empty_iff

set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
namespace VariableBound.Count
theorem _root_.solution (n : ℕ) (ψ : Fml) : #{ξ : Fin n → Bool | Vof ψ ξ = ∅} = nSat n ψ := by
  unfold nSat
  exact congrArg card (filter_congr fun ξ _ => Vof_eq_empty_iff ψ ξ)
end VariableBound.Count
