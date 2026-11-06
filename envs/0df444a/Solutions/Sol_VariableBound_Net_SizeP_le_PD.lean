-- Prove2me | solution 1 for VariableBound.Net.SizeP.le_PD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:35:28.338191+00:00
-- url     : https://prove2.me/submissions/ddfc11d6-e298-490a-ac62-1d438f725c02

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Net_SizeB
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_SizeP
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}
namespace VariableBound.Net.SizeP
theorem _root_.solution {tb rb x : ℕ} {sb : ℚ} (h : (x : ℚ) ≤ 2 * P0 g n Δ tb rb sb) : x ≤ PD g n Δ tb rb sb := by
  have h1 : (x : ℚ) ≤ (PD g n Δ tb rb sb : ℚ) := h.trans (Nat.le_ceil _)
  exact_mod_cast h1
end VariableBound.Net.SizeP
