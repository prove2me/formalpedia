-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.bitsOfTables_le_len
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:56:55.614125+00:00
-- url     : https://prove2.me/submissions/546ade14-830a-4849-b948-8511b9d49a82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_CountedToPadded_Tables
import Theorems.Thm_QueryMachines_Bridge_Proof_foldr_max_le
import Theorems.Thm_Groundwork_Prog_NetE_foldr_max_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_len_le_of_mem
import Theorems.Thm_Groundwork_two_le_len_list


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed
namespace QueryMachines.Bridge.Proof
theorem _root_.solution (T : Tab) : bitsOfTables T ≤ len T := by
  refine foldr_max_le ((by norm_num : 1 ≤ 2).trans (two_le_len_list T)) fun s hs => ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hs
  obtain ⟨r, hr, hzr⟩ := List.mem_flatten.1 hz
  have h1 := len_le_of_mem hzr
  have h2 := len_le_of_mem hr
  rw [len_int] at h1
  omega
end QueryMachines.Bridge.Proof
