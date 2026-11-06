-- Prove2me | solution 2 for QueryMachines.Tower.costSlowDown
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:26:21.355201+00:00
-- url     : https://prove2.me/submissions/893bda0a-c8be-4460-980e-4a548fcae918

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Cost
import Theorems.Thm_QueryMachines_Tower_costMono
import Theorems.Thm_QueryMachines_Tower_shapeS_mono
import Theorems.Thm_QueryMachines_Tower_shapeI_mono
import Theorems.Thm_QueryMachines_Tower_costShape
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
namespace QueryMachines.Tower
theorem _root_.solution : CostSlowDown := by
  intro own calls qs own' q' l x y hx
  induction l generalizing y with
  | zero =>
    show own 0 + calls 0 * 0 + qs 0 * (x * y) ≤ x * (own 0 + calls 0 * 0 + qs 0 * y)
    have e : x * (own 0 + calls 0 * 0 + qs 0 * y) = x * own 0 + qs 0 * (x * y) := by ring
    have h1 : own 0 ≤ x * own 0 := Nat.le_mul_of_pos_left _ hx
    rw [e]; omega
  | succ l ih =>
    rw [costShape, costShape]
    have e1 : x * (own' l + q' l * y + 2) = x * own' l + q' l * (x * y) + 2 * x := by ring
    have h0 : own' l ≤ x * own' l := Nat.le_mul_of_pos_left _ hx
    have hD := (costMono (shapeS_mono own calls qs) (shapeI_mono own' q') l (own' l + q' l * (x * y) + 2) (x * (own' l + q' l * y + 2)) (by rw [e1]; omega)).trans (ih _)
    generalize cost (shapeS own calls qs) (shapeI own' q') l (own' l + q' l * (x * y) + 2) = D at hD ⊢
    generalize cost (shapeS own calls qs) (shapeI own' q') l (own' l + q' l * y + 2) = C at hD ⊢
    have e : x * (own (l + 1) + calls (l + 1) * (C + 2) + qs (l + 1) * y) = x * own (l + 1) + calls (l + 1) * (x * C + 2 * x) + qs (l + 1) * (x * y) := by ring
    have h1 : own (l + 1) ≤ x * own (l + 1) := Nat.le_mul_of_pos_left _ hx
    have h2 : calls (l + 1) * (D + 2) ≤ calls (l + 1) * (x * C + 2 * x) := Nat.mul_le_mul_left _ (by omega)
    rw [e]; omega
end QueryMachines.Tower
