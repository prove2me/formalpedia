-- Prove2me | solution 1 for VariableBound.Net.Tuples.card_kP_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:52:29.578138+00:00
-- url     : https://prove2.me/submissions/9c41dd2e-f3f5-4c00-81ef-0352a4b97d55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_Net_Tuples
import Theorems.Thm_VariableBound_Net_Tuples_third_zero
import Theorems.Thm_VariableBound_Net_Tuples_card_sl
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}
namespace VariableBound.Net.Tuples
theorem _root_.solution (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) : #(kP D P 0) = #(sl D 0 0 P) := by
  rw [card_sl hW hP, kP]
  congr 1
  refine filter_congr fun o ho => ⟨fun h => ⟨h, third_zero (mem_range.1 (hP ho)) h⟩, fun h => h.1⟩
end VariableBound.Net.Tuples
