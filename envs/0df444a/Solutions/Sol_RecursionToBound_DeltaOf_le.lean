-- Prove2me | solution 1 for RecursionToBound.DeltaOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:57.350204+00:00
-- url     : https://prove2.me/submissions/e9f72e8e-a829-4864-b9e1-760acfb2cc3b

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
import Theorems.Thm_RecursionToBound_foldr_max_map_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_RecursionToBound_DeltaOf_eq
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]
namespace RecursionToBound
theorem _root_.solution (n : ℕ) (Φ : PFml) : SparsificationLemma.StepSparsify.DeltaOf n Φ ≤ Φ.length + 2 := by
  have h := foldr_max_map_le (occN Φ) (List.range n) (b := Φ.length) fun v => List.length_filter_le _ _
  rw [DeltaOf_eq]
  omega
end RecursionToBound
