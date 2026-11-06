-- Prove2me | solution 1 for RecursionToBound.DeltaOf_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:05.116186+00:00
-- url     : https://prove2.me/submissions/76b2867f-14eb-48f5-9e6f-8c1b3de142e4

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
import Theorems.Thm_RecursionToBound_DeltaOf_le
import Theorems.Thm_RecursionToBound_DeltaOf_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_of_length
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]
namespace RecursionToBound
theorem _root_.solution {n : α → ℕ} {Φ : α → PFml} (hn : Unary n) (hΦ : PolyT Φ) : Unary fun x => SparsificationLemma.StepSparsify.DeltaOf (n x) (Φ x) :=
  Unary.of_le (g := fun x => (Φ x).length + 2) ((Unary.of_length hΦ).add (Unary.const 2)) (DeltaOf_polyT hn hΦ) fun x => DeltaOf_le (n x) (Φ x)
end RecursionToBound
