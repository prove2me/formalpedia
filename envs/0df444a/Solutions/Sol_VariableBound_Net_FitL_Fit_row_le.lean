-- Prove2me | solution 1 for VariableBound.Net.FitL.Fit.row_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:45:30.955985+00:00
-- url     : https://prove2.me/submissions/44382cd8-760c-4f31-82ef-19cb966ad5e2

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
namespace Fit
theorem _root_.solution {k n Δ nb M : ℕ} {D : Dat} (hF : Fit k n Δ nb M D) : ∀ L ∈ D.2, L.length ≤ sbMax Δ := by
  intro L hL
  rcases Nat.lt_or_ge nb D.1.length with hlt | hle
  · exact FitL.row_le hF.isNb hF.m_le ((hF.big hlt).2.2 L hL)
  · rw [hF.small hle] at hL
    exact absurd hL List.not_mem_nil
end Fit
end VariableBound.Net.FitL
