-- Prove2me | solution 1 for Suffices.main_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:46:27.489998+00:00
-- url     : https://prove2.me/submissions/6a985e25-bf80-47af-925c-69762c35ab0f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Tactic.Ring
import Definitions.Def_Suffices_Sizes
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits
namespace Suffices
theorem _root_.solution {c c₁ c₂ A M N : ℕ} (hc : c = c₁ + A * (14 * M + 2) ^ A + 2 * A + c₂ + 22) (hN : 1 ≤ N) :
    c₁ * N ^ c₁ + A * ((14 * M + 2) * N ^ 2) ^ A ≤ c * N ^ c ∧ 20 * N ^ 2 ≤ c * N ^ c := by
  have e1 : N ^ c₁ ≤ N ^ c := Nat.pow_le_pow_right hN (by omega)
  have e2 : N ^ 2 ≤ N ^ c := Nat.pow_le_pow_right hN (by omega)
  have eA : N ^ (2 * A) ≤ N ^ c := Nat.pow_le_pow_right hN (by omega)
  generalize N ^ c = P at e1 e2 eA ⊢
  have hcP : c * P = c₁ * P + A * (14 * M + 2) ^ A * P + 2 * A * P + c₂ * P + 22 * P := by rw [hc]; ring
  have k1 : c₁ * N ^ c₁ ≤ c₁ * P := Nat.mul_le_mul_left _ e1
  have kA : A * ((14 * M + 2) * N ^ 2) ^ A ≤ A * (14 * M + 2) ^ A * P := by
    rw [mul_pow, ← pow_mul, ← mul_assoc]
    exact Nat.mul_le_mul_left _ eA
  rw [hcP]
  constructor <;> omega
end Suffices
