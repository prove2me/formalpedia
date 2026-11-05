-- Prove2me | solution 1 for QueryMachines.Tower.costSlowDown
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:50:08.13963+00:00
-- url     : https://prove2.me/submissions/103222c9-7a67-4525-8476-9327eb7729de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Cost
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower

namespace QueryMachines.Tower

/-- Dearer queries make the tower dearer, if they make the solver and the procedure dearer. -/
private theorem costMono_aux {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ}
    (hS : ∀ l tc tc' tq tq', tc ≤ tc' → tq ≤ tq' → TS l tc tq ≤ TS l tc' tq')
    (hI : ∀ l t t', t ≤ t' → TI l t ≤ TI l t') :
    ∀ l t t', t ≤ t' → cost TS TI l t ≤ cost TS TI l t'
  | 0, _, _, h => hS 0 _ _ _ _ le_rfl h
  | l + 1, _, _, h => hS _ _ _ _ _
      (Nat.add_le_add_right (costMono_aux hS hI l _ _
        (Nat.add_le_add_right (hI l _ _ h) 2)) 2) h

/-- The shape of the solver's cost is monotone in the two prices. -/
private theorem shapeS_mono_aux (own calls qs : ℕ → ℕ) (l tc tc' tq tq' : ℕ)
    (h1 : tc ≤ tc') (h2 : tq ≤ tq') :
    shapeS own calls qs l tc tq ≤ shapeS own calls qs l tc' tq' :=
  Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ h1) _) (Nat.mul_le_mul_left _ h2)

/-- The shape of the procedure's cost is monotone in the price. -/
private theorem shapeI_mono_aux (own' q' : ℕ → ℕ) (l t t' : ℕ) (h : t ≤ t') :
    shapeI own' q' l t ≤ shapeI own' q' l t' :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _

/-- The recursion written out for these shapes. -/
private theorem costShape_aux : CostShape := fun _ _ _ _ _ _ _ => rfl

end QueryMachines.Tower

theorem solution : CostSlowDown := by
  intro own calls qs own' q' l x y hx
  induction l generalizing y with
  | zero =>
    show own 0 + calls 0 * 0 + qs 0 * (x * y) ≤ x * (own 0 + calls 0 * 0 + qs 0 * y)
    have e : x * (own 0 + calls 0 * 0 + qs 0 * y) = x * own 0 + qs 0 * (x * y) := by ring
    have h1 : own 0 ≤ x * own 0 := Nat.le_mul_of_pos_left _ hx
    rw [e]
    omega
  | succ l ih =>
    rw [QueryMachines.Tower.costShape_aux, QueryMachines.Tower.costShape_aux]
    have e1 : x * (own' l + q' l * y + 2) = x * own' l + q' l * (x * y) + 2 * x := by ring
    have h0 : own' l ≤ x * own' l := Nat.le_mul_of_pos_left _ hx
    have hD := (QueryMachines.Tower.costMono_aux
      (QueryMachines.Tower.shapeS_mono_aux own calls qs)
      (QueryMachines.Tower.shapeI_mono_aux own' q') l
      (own' l + q' l * (x * y) + 2) (x * (own' l + q' l * y + 2))
      (by rw [e1]; omega)).trans (ih _)
    generalize cost (shapeS own calls qs) (shapeI own' q') l
      (own' l + q' l * (x * y) + 2) = D at hD ⊢
    generalize cost (shapeS own calls qs) (shapeI own' q') l
      (own' l + q' l * y + 2) = C at hD ⊢
    have e : x * (own (l + 1) + calls (l + 1) * (C + 2) + qs (l + 1) * y) =
        x * own (l + 1) + calls (l + 1) * (x * C + 2 * x) + qs (l + 1) * (x * y) := by ring
    have h1 : own (l + 1) ≤ x * own (l + 1) := Nat.le_mul_of_pos_left _ hx
    have h2 : calls (l + 1) * (D + 2) ≤ calls (l + 1) * (x * C + 2 * x) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [e]
    omega
