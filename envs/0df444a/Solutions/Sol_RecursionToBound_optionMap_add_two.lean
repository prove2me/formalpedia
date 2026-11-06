-- Prove2me | solution 1 for RecursionToBound.optionMap_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:55.171008+00:00
-- url     : https://prove2.me/submissions/e5100354-8505-4779-b79d-90ebd8b0bd8c

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
import Theorems.Thm_RecursionToBound_add_two_polyT
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]
namespace RecursionToBound
theorem _root_.solution {o : α → Option ℕ} {A B : α → ℕ} (ho : PolyT o) (hA : PolyT A) (hB : PolyT B) : PolyT fun x => (o x).map fun v => v + A x + B x :=
  PolyT.optionMap (f := fun x v => v + A x + B x) (add_two_polyT hA hB) ho
end RecursionToBound
