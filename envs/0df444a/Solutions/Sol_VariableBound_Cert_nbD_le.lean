-- Prove2me | solution 1 for VariableBound.Cert.nbD_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:11.497078+00:00
-- url     : https://prove2.me/submissions/a77b453a-2531-49d6-bab2-3d4ba6131fe6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Params_Cert
import Theorems.Thm_VariableBound_Cert_two_pow_log_le

set_option autoImplicit false
section
section
open VariableBound
open Groundwork AppVariables PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Cert
variable {α : Type} [Enc α]
namespace VariableBound.Cert
theorem _root_.solution (n Δ : ℕ) : nbD n Δ ≤ n + 1 := by
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) (two_pow_log_le n)
  have h := List.length_filter_le (fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)) (List.range (Nat.log 2 n + 1))
  rw [List.length_range] at h
  omega
end VariableBound.Cert
