-- Prove2me | solution 1 for UniformInK.CertTop.kcU_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:46:58.210112+00:00
-- url     : https://prove2.me/submissions/c5314d9b-6c0b-41b3-9e61-c54001232100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_UniformInK_Cert_Top
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_log_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open UniformInK UniformInK.CertTop
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
variable {α : Type} [Enc α]
variable {k K n s D : α → ℕ}
namespace UniformInK.CertTop
theorem _root_.solution (hk : Unary k) (hn : PolyT n) : Unary fun x => kcU (k x) (n x) :=
  hk.of_le (PolyT.min' hk.poly (log_polyT (hn.add (PolyT.const 1)))) fun _ => min_le_left _ _
end UniformInK.CertTop
