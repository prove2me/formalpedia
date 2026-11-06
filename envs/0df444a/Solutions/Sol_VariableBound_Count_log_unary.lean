-- Prove2me | solution 1 for VariableBound.Count.log_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:43:00.59233+00:00
-- url     : https://prove2.me/submissions/ac611079-c9e8-4b00-b092-8c074654b037

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Count_Cert
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8



set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg AppVariables VariableBound.Net
variable {α : Type} [Enc α]
namespace VariableBound.Count
theorem _root_.solution {n : α → ℕ} (hn : Unary n) : Unary fun x => Nat.log 2 (n x) :=
  Unary.of_le hn ((PolyT.log2' hn.poly).congr fun _ => Nat.log2_eq_log_two) fun _ => Nat.log_le_self _ _
end VariableBound.Count
