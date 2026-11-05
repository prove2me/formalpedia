-- Prove2me | solution 1 for VariableBound.Net.CertEv.PbD_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:38:23.714209+00:00
-- url     : https://prove2.me/submissions/084a300d-dfb3-4728-a07b-121a07148ea4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_PaddedDescent_F_CertEval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_CertEv
import Theorems.Thm_VariableBound_Net_CertEv_PD_natCast
import Theorems.Thm_PaddedDescent_F_Mark_Cert_qv_unary
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
theorem _root_.solution (K n Δ : ℕ) :
    PbD K n Δ = 2 * (qv (3 * K ^ 8) n * (1 + Δ * (tbMax n Δ + 3)) + qv (3 * K ^ 8) (10 * n) * sbMax Δ) :=
  PD_natCast _ _ _ _ _ _
end VariableBound.Net.CertEv
