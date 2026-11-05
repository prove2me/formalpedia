-- Prove2me | solution 1 for UniformInK.CertTop.blockU_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:27:49.907125+00:00
-- url     : https://prove2.me/submissions/4c9acb2b-05f0-4bc8-9206-728596562bfe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_UniformInK_Cert_Top
import Theorems.Thm_UniformInK_CertTop_powBetaU_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open UniformInK UniformInK.CertTop
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
variable {α : Type} [Enc α]
variable {k K n s D : α → ℕ}
namespace UniformInK.CertTop
theorem _root_.solution (hk : Unary k) (hn : Unary n) (hs : Unary s) : Unary fun x => blockU (k x) (n x) (s x) := by
  have h2 : Unary fun x => n x + 1 := hn.add (Unary.const 1)
  exact h2.of_le (PolyT.min' (powBetaU_polyT hk hs) h2.poly) fun _ => min_le_right _ _
end UniformInK.CertTop
