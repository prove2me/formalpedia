-- Prove2me | solution 1 for VariableBound.Net.CertNet.sig_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:33:55.729033+00:00
-- url     : https://prove2.me/submissions/ce20a766-e08e-485b-b7b7-608bc74118f8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
import Theorems.Thm_VariableBound_Net_CertNet_ite_zero_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_powZ_polyT
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_PaddedDescent_F_Mark_Cert_sign_polyT
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.sign_polyT



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]
namespace VariableBound.Net.CertNet
theorem _root_.solution {i : α → ℕ} (hi : Unary i) : PolyT fun x => ParityChecks.sig (i x) := by
  have h1 : PolyT fun x => (2 : ℤ) ^ (i x - 1) := powZ_polyT (PolyT.const 2) (unary_sub hi (PolyT.const 1))
  have h2 : PolyT fun x => (-1 : ℤ) ^ i x := Mark.Cert.sign_polyT hi.poly
  exact ite_zero_polyT hi.poly (PolyT.const 1) (PolyT.mulZ h2 h1)
end VariableBound.Net.CertNet
