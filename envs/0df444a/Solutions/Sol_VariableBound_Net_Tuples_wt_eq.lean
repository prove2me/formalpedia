-- Prove2me | solution 1 for VariableBound.Net.Tuples.wt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:30:16.101968+00:00
-- url     : https://prove2.me/submissions/071aa36b-cf88-4235-b51c-84a875513d02

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
import Theorems.Thm_VariableBound_Net_Tuples_length_chks
import Theorems.Thm_VariableBound_Net_Tuples_card_kP_zero
import Theorems.Thm_VariableBound_Net_Tuples_card_chP
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
theorem _root_.solution (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (fl : Bool) :
    wt D fl P = (bif fl then (-1) ^ #(sl D 0 0 P) else 1) * ∏ j : Fin (chks D).length, ParityChecks.sig #(sl D 1 j.val P) := by
  rw [wt, Fin.prod_univ_eq_prod_range (fun j => ParityChecks.sig #(sl D 1 j P)), length_chks, card_kP_zero hW hP, mul_comm]
  congr 1
  exact prod_congr rfl fun j _ => by rw [card_chP hW hP]
end VariableBound.Net.Tuples
