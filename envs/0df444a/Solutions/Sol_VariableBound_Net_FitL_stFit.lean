-- Prove2me | solution 1 for VariableBound.Net.FitL.stFit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:36:09.053575+00:00
-- url     : https://prove2.me/submissions/68e8db59-e9f4-467a-8492-f740d9e53b65

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
theorem _root_.solution : StFit := by
  intro k n Δ nb rb tb M ψ L hW hΔ hocc hm hnb hM
  refine ⟨fun hlt hS hrb hrM h1 htb => ?_, fun hle => ?_⟩
  · obtain ⟨hl, hrow, hcol⟩ := hS
    exact
      { wf := ⟨hW, fun l hl' => ⟨(hrow l hl').1.imp fun h => ne_of_lt h, (hrow l hl').2.1⟩⟩
        two := hΔ
        occ_le := hocc
        m_le := hm
        isNb := hnb
        M_le := hM
        r_le := hl.trans hrb
        col := fun e he => (hcol e he).trans (by omega)
        big := fun _ => ⟨hl.trans hrM, h1, fun l hl' => (hrow l hl').2.2⟩
        small := fun h => absurd h (Nat.not_le.2 hlt) }
  · exact
      { wf := ⟨hW, fun l hl' => absurd hl' List.not_mem_nil⟩
        two := hΔ
        occ_le := hocc
        m_le := hm
        isNb := hnb
        M_le := hM
        r_le := Nat.zero_le _
        col := fun e _ => Nat.zero_le _
        big := fun h => absurd hle (Nat.not_le.2 h)
        small := fun _ => rfl }
end VariableBound.Net.FitL
