-- Prove2me | solution 1 for VariableBound.Net.stCertRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:59:53.28387+00:00
-- url     : https://prove2.me/submissions/7fcf1b09-774c-4f81-b04d-117fec27769e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Rank
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertRank
import Theorems.Thm_VariableBound_Net_CertRank_rank_polyT
import Theorems.Thm_VariableBound_Net_CertRank_choose_min
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min_right
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_choose_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_clog_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_min_right
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
open CertRank
namespace VariableBound.Net
theorem _root_.solution : StCertRank := by
  refine ⟨fun α _ t μ ht hμ => choose_polyT ht.poly hμ, rank_polyT, fun α _ t μ ht hμ => ?_⟩
  have h1 : Unary fun x => min (μ x) (t x + 1) := unary_min_right hμ (ht.add (Unary.const 1))
  have h2 : PolyT fun x => (t x).choose (min (μ x) (t x + 1)) := choose_polyT ht.poly h1
  unfold cw
  exact clog_unary (h2.congr fun x => choose_min _ _)
end VariableBound.Net
