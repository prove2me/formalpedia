-- Prove2me | solution 1 for Printed.stAlgorithm_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:24:25.617271+00:00
-- url     : https://prove2.me/submissions/d4bef894-7faf-4f2f-820e-5c819679b4b8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Proof
import Theorems.Thm_Printed_decidesSparse_of_cost
import Theorems.Thm_Eight_Level_firstLevel_spec
import Theorems.Thm_P2M_Eight_delta__le_fd4e6e087c27


set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Eight Eight.SecNetworks Paper QueryMachines
namespace Printed
theorem _root_.solution (hS : Suffices.StSuffices) (hCC : StCountCost) : StAlgorithm := by
  intro δ Mc τ hδ' hδ hδ1 hM hE
  have hM' : (1 : ℝ) ≤ Mc := by exact_mod_cast hM
  have h3 := Eight.delta'_le hδ1 hM'
  obtain ⟨hK, hLe⟩ := Eight.Level.firstLevel_spec hδ'
  obtain ⟨hp, A, hA⟩ := hCC _ (Eight.Level.firstLevel hδ') hδ' (by linarith) hK hLe
  have hs := hS δ Mc τ hδ hM hE
  exact ⟨hs.1 _ hp, hs.2 _ A (decidesSparse_of_cost hA)⟩
end Printed
