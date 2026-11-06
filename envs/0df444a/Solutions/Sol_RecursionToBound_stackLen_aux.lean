-- Prove2me | solution 1 for RecursionToBound.stackLen_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:13:55.67025+00:00
-- url     : https://prove2.me/submissions/21f62d6e-a3af-464d-bc3b-d3eeb260b0f9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Thresholds
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_PaddedDescent_F_CertEval
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_RecursionToBound_Cert_Exponent
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]
namespace RecursionToBound
theorem _root_.solution {b p m k n : α → ℕ} (hb : PolyT b) (hp : PolyT p) (hm : PolyT m) (hk : PolyT k) (hn : PolyT n) :
    PolyT fun x => (b x * n x + 1) * (p x * m x * (k x * (3 * n x + 5) + 10) + 2 * n x * (2 * (3 * n x + 5) + 10) + 8) + 3 * n x + 16 := by
  have h35 : PolyT fun x => 3 * n x + 5 := ((PolyT.const 3).mul hn).add (PolyT.const 5)
  exact ((((hb.mul hn).add (PolyT.const 1)).mul
    ((((hp.mul hm).mul ((hk.mul h35).add (PolyT.const 10))).add (((PolyT.const 2).mul hn).mul (((PolyT.const 2).mul h35).add (PolyT.const 10)))).add (PolyT.const 8))).add
      ((PolyT.const 3).mul hn)).add (PolyT.const 16)
end RecursionToBound
