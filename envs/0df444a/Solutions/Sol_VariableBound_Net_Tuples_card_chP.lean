-- Prove2me | solution 1 for VariableBound.Net.Tuples.card_chP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:59:14.231201+00:00
-- url     : https://prove2.me/submissions/1eaaf98b-d8f5-4830-9356-96491272ad14

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
import Theorems.Thm_VariableBound_Net_Tuples_card_sl
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
theorem _root_.solution (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (j : ℕ) : #(chP D P j) = #(sl D 1 j P) := by
  rw [card_sl hW hP, chP]
end VariableBound.Net.Tuples
