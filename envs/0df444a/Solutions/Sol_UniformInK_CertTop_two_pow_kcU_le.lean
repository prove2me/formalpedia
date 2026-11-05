-- Prove2me | solution 1 for UniformInK.CertTop.two_pow_kcU_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:29:52.680207+00:00
-- url     : https://prove2.me/submissions/0f0f8070-d8ea-4d65-9bb4-2ed9df058ffd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_UniformInK_Cert_Top
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open UniformInK UniformInK.CertTop
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
variable {α : Type} [Enc α]
variable {k K n s D : α → ℕ}
namespace UniformInK.CertTop
theorem _root_.solution (k n : ℕ) : 2 ^ kcU k n ≤ n + 1 :=
  (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)).trans (Nat.pow_log_le_self 2 (by omega))
end UniformInK.CertTop
