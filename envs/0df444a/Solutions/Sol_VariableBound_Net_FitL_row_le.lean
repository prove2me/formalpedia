-- Prove2me | solution 1 for VariableBound.Net.FitL.row_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:04.586523+00:00
-- url     : https://prove2.me/submissions/c944cc19-2f11-42b1-ac7f-dd9e2c6083f0

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
import Theorems.Thm_VariableBound_Net_FitL_nb_pos
import Theorems.Thm_VariableBound_Net_FitL_n_lt
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
theorem _root_.solution {n Δ nb m l : ℕ} (h : AppVariables.IsNb n Δ nb) (hm : m ≤ Δ * n) (hl : nb * l ≤ 16 * m) : l ≤ sbMax Δ := by
  refine Nat.le_of_mul_le_mul_left ?_ (nb_pos h)
  unfold sbMax
  calc nb * l ≤ 16 * (Δ * n) := hl.trans (Nat.mul_le_mul_left _ hm)
    _ ≤ 16 * (Δ * (LD Δ * (2 * nb))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (n_lt h).le)
    _ = nb * (32 * Δ * LD Δ) := by ring
end VariableBound.Net.FitL
