-- Prove2me | solution 1 for VariableBound.Net.CertEv.UbD_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:53:56.06178+00:00
-- url     : https://prove2.me/submissions/83e61648-8698-4d75-89f5-12e7a60c9092

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_PaddedDescent_F_CertEval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_CertEv
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_clog_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_LD_unary
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
theorem _root_.solution {k K n Δ : α → ℕ} (hk : Unary k) (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => UbD (k x) (K x) (n x) (Δ x) :=
  ((((Unary.const 6).mul hk).mul (hn.add (LD_unary hΔ.poly))).add
    ((((Unary.const 28).mul hk).mul hn).mul (clog_unary (((PolyT.const 96).mul hΔ.poly).mul (LD_unary hΔ.poly).poly)))).add
    ((Unary.const 2).mul (unary_pow_const (g_unary hK) 2))
end VariableBound.Net.CertEv
