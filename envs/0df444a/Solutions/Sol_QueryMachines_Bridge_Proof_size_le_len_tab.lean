-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.size_le_len_tab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:21.111885+00:00
-- url     : https://prove2.me/submissions/8b778fa3-8640-43f4-a3db-ec503bf935fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_CountedToPadded_Tables
import Theorems.Thm_QueryMachines_Bridge_Proof_size_le_len_list
import Theorems.Thm_Groundwork_size_int
attribute [local simp] Groundwork.size_int



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed
namespace QueryMachines.Bridge.Proof
theorem _root_.solution (T : Tab) : size T ≤ len T :=
  size_le_len_list T fun r _ => size_le_len_list r fun z _ => by rw [size_int, len_int]; omega
end QueryMachines.Bridge.Proof
