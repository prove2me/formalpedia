-- Prove2me | solution 1 for RecursionToBound.powWidthCut_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:56.253697+00:00
-- url     : https://prove2.me/submissions/6529195d-db2d-43b7-9627-224b65ab97e9

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
import Theorems.Thm_RecursionToBound_widthU_unary
import Theorems.Thm_RecursionToBound_nU_unary
import Theorems.Thm_PaddedDescent_F_CertNet_nU
import Theorems.Thm_UniformInK_CertTop_powKcU_unary
attribute [local fun_prop] PaddedDescent.F.CertNet.nU



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]
namespace RecursionToBound
theorem _root_.solution : Unary fun x : List Bool => 2 ^ kcU (widthU x) (nU x) := powKcU_unary widthU_unary nU_unary
end RecursionToBound
