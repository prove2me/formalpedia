-- Prove2me | solution 1 for VariableBound.Net.FitL.nb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:35:58.012203+00:00
-- url     : https://prove2.me/submissions/b2913574-8a59-44c1-a188-2913b77fc2d3

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
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
theorem _root_.solution {n Δ nb : ℕ} (h : AppVariables.IsNb n Δ nb) (hΔ : 1 ≤ Δ) : nb ≤ n :=
  (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 ((Nat.pow_le_pow_left (by omega : 2 ≤ 2 * Δ) nb).trans h.2.1)
end VariableBound.Net.FitL
