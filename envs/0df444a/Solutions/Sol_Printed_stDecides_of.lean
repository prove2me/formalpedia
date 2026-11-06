-- Prove2me | solution 1 for Printed.stDecides_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:14:17.176905+00:00
-- url     : https://prove2.me/submissions/53329c83-4437-403b-bbbd-e472340ec5bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Proof
import Theorems.Thm_Eight_decidesInSteps_mono


set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Eight Eight.SecNetworks Paper QueryMachines
namespace Printed
theorem _root_.solution (hAlg : StAlgorithm) (hEn : Enumerate.StEnumeration) : StDecides := by
  intro δ hδ
  have hδ₀ : 0 < min δ 1 := lt_min hδ one_pos
  obtain ⟨M, τ, hM, hE⟩ := hEn (min δ 1 / 3) (by linarith)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hδ' : 0 < min δ 1 / (3 * (M : ℝ)) := div_pos hδ₀ (by linarith)
  obtain ⟨hp, hd⟩ := hAlg (min δ 1) M τ hδ' hδ₀ (min_le_right _ _) hM hE
  exact ⟨_, τ, hp, Eight.decidesInSteps_mono hd (min_le_left _ _)⟩
end Printed
