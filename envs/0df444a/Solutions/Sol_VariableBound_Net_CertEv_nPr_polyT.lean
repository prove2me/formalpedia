-- Prove2me | solution 1 for VariableBound.Net.CertEv.nPr_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:40:27.935833+00:00
-- url     : https://prove2.me/submissions/deff2090-b473-4ebb-8c6d-4b3b228e293a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_PaddedDescent_F_CertEval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_CertEv
import Theorems.Thm_VariableBound_Net_CertEv_objs_polyT
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_PaddedDescent_F_CertEval_nProf_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_qv_unary
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
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
theorem _root_.solution {g : α → ℕ} {D : α → Dat} (hg : Unary g) (hD : PolyT D) : PolyT fun x => nPr (g x) (D x) :=
  nProf_polyT hg (PolyT.length (objs_polyT hD)) (Unary.const 2)
end VariableBound.Net.CertEv
