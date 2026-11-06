-- Prove2me | solution 1 for VariableBound.CertTop.restD_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:07:17.011797+00:00
-- url     : https://prove2.me/submissions/d04dd316-f3c1-4dc7-af9d-7a7d049c245d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Cert_Top
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_LD_polyT
import Theorems.Thm_ClauseBound_TopN_Cert_lamS_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.pow_const



set_option autoImplicit false
section
section
open VariableBound VariableBound.CertTop
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound.Net VariableBound.Net.CertEv
open ClauseBound.TopN.Cert (lamS_unary)
open ClauseBound.ParityChecks.CertTopOL (LD_polyT)
variable {α : Type} [Enc α]
variable {k K n s : α → ℕ}
namespace VariableBound.CertTop
theorem _root_.solution {Z₁ Z₂ B z q : α → ℕ} (hk : PolyT k) (hK : PolyT K) (h1 : PolyT Z₁) (h2 : PolyT Z₂) (hB : PolyT B) (hz : PolyT z) (hn : PolyT n) (hq : PolyT q) :
    PolyT fun x => 3 * K x ^ 8 * (3 * K x ^ 8) * 2 * Z₁ x + Z₂ x + (n x / q x + 2) + (B x + 5 * k x + 10 + (k x + 3) * z x) := by
  have h8 : PolyT fun x => 3 * K x ^ 8 := (PolyT.const 3).mul (hK.pow_const 8)
  exact (((((h8.mul h8).mul (PolyT.const 2)).mul h1).add h2).add
    ((PolyT.div hn hq).add (PolyT.const 2))).add (((hB.add ((PolyT.const 5).mul hk)).add (PolyT.const 10)).add ((hk.add (PolyT.const 3)).mul hz))
end VariableBound.CertTop
