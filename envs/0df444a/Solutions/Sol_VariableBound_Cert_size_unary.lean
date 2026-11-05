-- Prove2me | solution 1 for VariableBound.Cert.size_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:28.095129+00:00
-- url     : https://prove2.me/submissions/3ecb4961-ba93-471f-afa8-d83ad8184f4c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Params_Cert
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_congr
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_clog_two_eq
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_clog_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_congr
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open VariableBound
open Groundwork AppVariables PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Cert
variable {α : Type} [Enc α]
namespace VariableBound.Cert
theorem _root_.solution {m : α → ℕ} (hm : PolyT m) : Unary fun x => Nat.size (m x) :=
  unary_congr (clog_unary (hm.add (PolyT.const 1))) fun x => by rw [clog_two_eq, Nat.add_sub_cancel]
end VariableBound.Cert
