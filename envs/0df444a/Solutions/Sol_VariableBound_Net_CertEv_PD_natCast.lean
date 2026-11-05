-- Prove2me | solution 1 for VariableBound.Net.CertEv.PD_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:29:42.053415+00:00
-- url     : https://prove2.me/submissions/fbd6e78c-9a37-46fa-b6c7-407a0c057c5b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_PaddedDescent_F_CertEval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_CertEv
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
theorem _root_.solution (g n Δ tb rb sb : ℕ) : PD g n Δ tb rb (sb : ℚ) = 2 * (qv g n * (1 + Δ * (tb + 3)) + qv g rb * sb) := by
  unfold PD P0
  have h : 2 * ((qv g n : ℚ) * (1 + Δ * (tb + 3)) + (qv g rb : ℚ) * sb) = ((2 * (qv g n * (1 + Δ * (tb + 3)) + qv g rb * sb) : ℕ) : ℚ) := by
    push_cast; ring
  rw [h, Nat.ceil_natCast]
end VariableBound.Net.CertEv
