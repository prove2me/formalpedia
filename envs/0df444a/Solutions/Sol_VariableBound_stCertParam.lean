-- Prove2me | solution 1 for VariableBound.stCertParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:48:22.357118+00:00
-- url     : https://prove2.me/submissions/1a68b87a-af71-4be6-a367-2860d2533456

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Params_Cert
import Theorems.Thm_VariableBound_Cert_nbD_unary
import Theorems.Thm_VariableBound_Cert_beta_unary
import Theorems.Thm_VariableBound_Cert_rbD_unary
import Theorems.Thm_VariableBound_Cert_tbD_unary
import Theorems.Thm_Groundwork_Unary_poly


set_option autoImplicit false
section
section
open VariableBound
open Groundwork AppVariables PaddedDescent.F ClauseBound.ParityChecks.CertLib
namespace VariableBound
theorem _root_.solution : StCertParam := fun _ _ _ _ _ _ _ _ hn hΔ hm hβ hnb hrb =>
  ⟨Cert.nbD_unary hn hΔ.poly, Cert.beta_unary hn hm.poly hnb, Cert.rbD_unary hβ, Cert.tbD_unary hm.poly hnb.poly hrb⟩
end VariableBound
