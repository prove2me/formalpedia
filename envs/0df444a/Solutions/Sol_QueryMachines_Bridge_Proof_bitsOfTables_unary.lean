-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.bitsOfTables_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:03.397194+00:00
-- url     : https://prove2.me/submissions/59870b40-b5a3-46ea-9261-c05bd3eefc78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_CountedToPadded_Tables
import Theorems.Thm_QueryMachines_Bridge_Proof_bitsOfTables_poly
import Theorems.Thm_QueryMachines_Bridge_Proof_len_tab_unary
import Theorems.Thm_QueryMachines_Bridge_Proof_bitsOfTables_le_len
import Theorems.Thm_Groundwork_Unary_of_le


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed
namespace QueryMachines.Bridge.Proof
theorem _root_.solution : Unary bitsOfTables := Unary.of_le len_tab_unary bitsOfTables_poly bitsOfTables_le_len
end QueryMachines.Bridge.Proof
