-- Prove2me | solution 1 for RecursionToBound.plan_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:58.343688+00:00
-- url     : https://prove2.me/submissions/fecc9771-0331-4ebe-a35d-bcf2bbb8f590

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
import Theorems.Thm_RecursionToBound_planAt_polyT
import Theorems.Thm_RecursionToBound_nU_unary
import Theorems.Thm_RecursionToBound_widthCut_unary
import Theorems.Thm_RecursionToBound_idxU_polyT
import Theorems.Thm_RecursionToBound_numU_polyT

set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
namespace RecursionToBound
theorem _root_.solution (hP : S.Poly) (n₁ : ℕ) {pick : U → U × Idx} {num : U × U → ℕ × ℕ} (hpick : PolyT pick) (hnum : PolyT num) : PolyT (plan S n₁ pick num) :=
  planAt_polyT S hP n₁ widthCut_unary nU_unary (idxU_polyT hpick) (numU_polyT S hP hpick hnum)
end RecursionToBound
