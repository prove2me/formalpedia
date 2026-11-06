-- Prove2me | solution 1 for VariableBound.Net.FitL.stNPrMax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:20.94321+00:00
-- url     : https://prove2.me/submissions/1fc249fd-e1a0-43b4-817a-374eb1d89807

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
import Theorems.Thm_VariableBound_Net_FitL_row_le
import Theorems.Thm_VariableBound_Net_FitL_Fit_row_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_r_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
theorem _root_.solution (h : StNPr) : StNPrMax := by
  intro k K n Δ nb M D hF
  have h1 := (h (3 * K ^ 8) D (sbMax Δ) (Fit.row_le hF)).1
  unfold nPr nPrMax nProf objMax
  exact Nat.pow_le_pow_left (Nat.succ_le_succ (h1.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hF.r_le) hF.m_le))) _
end VariableBound.Net.FitL
