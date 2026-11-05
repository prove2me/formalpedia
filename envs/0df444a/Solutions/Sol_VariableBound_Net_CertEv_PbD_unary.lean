-- Prove2me | solution 1 for VariableBound.Net.CertEv.PbD_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:51:12.964059+00:00
-- url     : https://prove2.me/submissions/82f383e5-4703-417b-8f9c-36ba59f3a923

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_PaddedDescent_F_CertEval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_CertEv
import Theorems.Thm_VariableBound_Net_CertEv_PbD_eq
import Theorems.Thm_VariableBound_Net_CertEv_tbMax_unary
import Theorems.Thm_VariableBound_Net_CertEv_sbMax_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_congr
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_congr
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_g_unary
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_PaddedDescent_F_Mark_Cert_qv_unary
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.qv_unary



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertEv
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertEval ClauseBound.Alg ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
open PaddedDescent.F.Mark (qv nProf)
open PaddedDescent.F.Mark.Cert (qv_unary)
variable {α : Type} [Enc α]
namespace VariableBound.Net.CertEv
theorem _root_.solution {K n Δ : α → ℕ} (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => PbD (K x) (n x) (Δ x) :=
  unary_congr ((Unary.const 2).mul
    (((qv_unary (g_unary hK) hn).mul ((Unary.const 1).add (hΔ.mul ((tbMax_unary hn.poly hΔ.poly).add (Unary.const 3))))).add
      ((qv_unary (g_unary hK) ((Unary.const 10).mul hn)).mul (sbMax_unary hΔ)))) fun x => (PbD_eq (K x) (n x) (Δ x)).symm
end VariableBound.Net.CertEv
