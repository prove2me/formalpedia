-- Prove2me | solution 1 for VariableBound.Cert.beta_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:25.867337+00:00
-- url     : https://prove2.me/submissions/f97d052c-a438-4e3b-a088-1b6857c78484

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Params_Cert
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_choose_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_clog_unary
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
theorem _root_.solution {n m nb : α → ℕ} (hn : Unary n) (hm : PolyT m) (hnb : Unary nb) : Unary fun x => beta (n x) (m x) (nb x) :=
  (hn.add (clog_unary (choose_polyT hm (hnb.add (Unary.const 1))))).add (Unary.const 1)
end VariableBound.Cert
