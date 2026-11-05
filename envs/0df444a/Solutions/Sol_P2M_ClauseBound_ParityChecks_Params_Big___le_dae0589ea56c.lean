-- Prove2me | solution 1 for P2M_ClauseBound_ParityChecks_Params_Big___le_dae0589ea56c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:12:13.172851+00:00
-- url     : https://prove2.me/submissions/5b4ea858-183b-48d0-ae5b-c6a9f7f2a8db

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_succ_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b
namespace ClauseBound.ParityChecks.Params.Big
theorem _root_.solution : Δ ≤ 2 ^ (c * t) := by
  calc Δ ≤ (ℓ + 1) ^ c := b.hΔ
    _ ≤ (2 ^ t) ^ c := Nat.pow_le_pow_left b.succ_le c
    _ = 2 ^ (c * t) := by rw [← pow_mul, mul_comm]
end ClauseBound.ParityChecks.Params.Big
