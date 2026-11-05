-- Prove2me | solution 1 for P2M_ClauseBound_ParityChecks_Params_two___le_d18f4ddaa33d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:57:40.881497+00:00
-- url     : https://prove2.me/submissions/c334563e-acd5-4770-a911-6127fba5a63e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
namespace ClauseBound.ParityChecks.Params
theorem _root_.solution (Δ : ℕ) : 2 * Δ ≤ 2 ^ LD Δ := Nat.le_pow_clog (by norm_num) _
end ClauseBound.ParityChecks.Params
