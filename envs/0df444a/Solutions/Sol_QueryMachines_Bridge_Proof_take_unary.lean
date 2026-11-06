-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.take_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:42.488069+00:00
-- url     : https://prove2.me/submissions/b4334f25-cc95-45e4-bf77-728b2e4ae8f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_CountedToPadded_Pick
import Theorems.Thm_QueryMachines_Bridge_Proof_eq_unary
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels
namespace QueryMachines.Bridge.Proof
theorem _root_.solution (b : U) {l : ℕ} (h : l ≤ b.length) : b.take l = unary l := by
  rw [eq_unary (b.take l), List.length_take, min_eq_left h]
end QueryMachines.Bridge.Proof
