-- Prove2me | solution 1 for VariableBound.Net.SizeP.sum_capD_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:43:53.833136+00:00
-- url     : https://prove2.me/submissions/489a6d8d-8059-47a0-8cc1-8d1310503e75

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
import Theorems.Thm_VariableBound_Net_SizeP_cw_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_VariableBound_Net_Tests_capD_eq
import Theorems.Thm_VariableBound_Net_Tests_sum_length_tst_node_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}
namespace VariableBound.Net.SizeP
theorem _root_.solution (y : ℕ) {a : ℕ} (ha : a < g) : ∑ b ∈ (range g).erase a, capD g n D y a b ≤ 2 * (tch g n D a).length := by
  refine le_trans (sum_le_sum fun b _ => ?_) (Tests.sum_length_tst_node_le ha)
  rw [Tests.capD_eq]
  exact sum_le_sum fun κ _ => cw_le _ _
end VariableBound.Net.SizeP
