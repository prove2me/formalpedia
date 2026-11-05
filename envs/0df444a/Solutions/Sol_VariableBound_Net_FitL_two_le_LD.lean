-- Prove2me | solution 1 for VariableBound.Net.FitL.two_le_LD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:31:56.664303+00:00
-- url     : https://prove2.me/submissions/38157ad3-be76-43f2-a98d-25d9e94459e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_VariableBound_Net_Fit

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
theorem _root_.solution {Δ : ℕ} (hΔ : 2 ≤ Δ) : 2 ≤ LD Δ := by
  have h : Nat.clog 2 (2 ^ 2) ≤ Nat.clog 2 (2 * Δ) := Nat.clog_mono_right 2 (by omega)
  rwa [Nat.clog_pow 2 2 (by norm_num)] at h
end VariableBound.Net.FitL
