-- Prove2me | solution 1 for Wrap.coding_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:08:40.351374+00:00
-- url     : https://prove2.me/submissions/104f0e27-872c-461e-9bf1-14ab0b831d2a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_CodingExists
import Theorems.Thm_Wrap_Conf_stepOf_polyT
import Theorems.Thm_Wrap_Conf_stepOf_repOf
import Theorems.Thm_Wrap_Conf_initOf_polyT
import Theorems.Thm_Wrap_Conf_initOf_eq
import Theorems.Thm_Wrap_Conf_outOf_polyT
import Theorems.Thm_Wrap_Conf_outOf_halted
import Theorems.Thm_Wrap_Conf_outOf_running
import Theorems.Thm_Wrap_Conf_size_repOf_stay_le
import Theorems.Thm_Wrap_Conf_size_initOf_le
import Theorems.Thm_CircuitLowerBound_Tab_Enc_step
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab Conf
namespace Wrap
theorem _root_.solution (M : TM2ComputableAux Bool Bool) (hfin : ∀ i, Finite (M.tm.Γ i)) : Nonempty (Coding M) :=
  ⟨{ rep := repOf M
     step := stepOf M
     init := initOf M
     out := outOf M
     a := (2 * bnd M + (ks M).length * (2 * dep M * (bnd M + 1))) + (2 * bnd M + (ks M).length * (bnd M + 3) + 1)
     step_poly := stepOf_polyT M
     init_poly := initOf_polyT M
     out_poly := outOf_polyT M
     step_rep := stepOf_repOf M
     init_rep := initOf_eq M
     out_halted := outOf_halted M
     out_running := outOf_running M
     size_init := fun x => (size_initOf_le M x).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
     size_step := fun c => (size_repOf_stay_le M c).trans (Nat.add_le_add_left (Nat.le_add_right _ _) _) }⟩
end Wrap
