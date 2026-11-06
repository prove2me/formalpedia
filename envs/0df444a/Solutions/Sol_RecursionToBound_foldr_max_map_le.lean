-- Prove2me | solution 1 for RecursionToBound.foldr_max_map_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:30:43.028219+00:00
-- url     : https://prove2.me/submissions/37ca0e4b-99fd-4a60-85b3-e016fe482403

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]
namespace RecursionToBound
theorem _root_.solution {β : Type} (f : β → ℕ) (l : List β) {b : ℕ} (h : ∀ a, f a ≤ b) : (l.map f).foldr max 0 ≤ b := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons]
    exact max_le (h a) ih
end RecursionToBound
