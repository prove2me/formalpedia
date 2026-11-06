-- Prove2me | solution 1 for RecursionToBound.countIsPolynomialTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:20:56.749229+00:00
-- url     : https://prove2.me/submissions/cea159a3-91ee-489f-88ab-b4e5a5f05168

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Exponent
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_StepSparsify_CertWalk
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_RecursionToBound_Cert_Top
import Theorems.Thm_RecursionToBound_count_polyT
import Theorems.Thm_RecursionToBound_expo_polyT
import Theorems.Thm_VariableBound_certCountDc


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]
namespace RecursionToBound
theorem _root_.solution : CountIsPolynomialTime :=
  fun _ _ S hP n₁ _ _ hpick hnum => ⟨count_polyT S certCountDc hP n₁ hpick hnum, expo_polyT S hP n₁ hpick hnum⟩
end RecursionToBound
