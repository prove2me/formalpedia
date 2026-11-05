-- Prove2me | solution 1 for P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:27:13.023968+00:00
-- url     : https://prove2.me/submissions/775f8810-40f0-4769-a85b-1d1b77be2c74

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
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b
namespace ClauseBound.ParityChecks.Params.Big
theorem _root_.solution : 84 * (c * t) + 84 * t ≤ ℓ := by
  have h := b.hA
  have e : 84 * (c + 1) * t = 84 * (c * t) + 84 * t := by ring
  omega
end ClauseBound.ParityChecks.Params.Big
