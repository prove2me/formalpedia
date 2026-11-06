-- Prove2me | solution 1 for RecursionToBound.stackLen_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:25:56.072961+00:00
-- url     : https://prove2.me/submissions/3eddf7a2-e1bd-409d-b129-ee69f05d7e18

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
import Theorems.Thm_RecursionToBound_stackLen_aux
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_two_pow
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]
namespace RecursionToBound
theorem _root_.solution {k τ n : α → ℕ} (hk : Unary k) (hτ : PolyT τ) (hn : PolyT n) : PolyT fun x => stackLenCU (k x) (τ x) (n x) (inLen (k x) (n x)) := by
  have hk' := hk.poly
  have hb : PolyT fun x => τ x ^ (2 * k x) := PolyT.pow_unary hτ ((Unary.const 2).mul hk)
  have hp : PolyT fun x => 2 ^ k x := PolyT.two_pow hk
  have hm : PolyT fun x => (k x * 2 ^ k x + 1) * (n x + 2) ^ (k x + 1) :=
    ((hk'.mul hp).add (PolyT.const 1)).mul (PolyT.pow_unary (hn.add (PolyT.const 2)) (hk.add (Unary.const 1)))
  unfold stackLenCU bsumU inLen
  exact stackLen_aux hb hp hm hk' hn
end RecursionToBound
