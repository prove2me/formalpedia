-- Prove2me | solution 1 for P2M_TwoMachines_exists_bound__28fef89684c0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:50:58.554071+00:00
-- url     : https://prove2.me/submissions/d768b1c5-5c32-4484-90e0-2b78a6e4b657

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_TwoMachines_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_TwoMachines_Main
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mono_bound
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PB_pow
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}
namespace TwoMachines
theorem _root_.solution (q₀ a₁ a₂ c₁ c₂ : ℕ) : ∃ q : ℕ, ∀ t n p₁ p₂ : ℕ, p₁ ≤ c₁ * (3 * n + 2 + 1) ^ c₁ → p₂ ≤ c₂ * (3 * n + 2 + 1) ^ c₂ →
    q₀ * (t + 1) * (n + (a₁ * (p₁ + 1) + a₁ * t + (a₂ * (p₂ + 1) + a₂ * t)) + 1) ^ q₀ ≤ q * (t + n + 1) ^ q := by
  have pP : ∀ c : ℕ, PB fun m => c * (3 * m + 2 + 1) ^ c := fun c => (PB.mono_bound c).1.comp (((PB.const 3).mul PB.id').add (PB.const 2))
  have pG : PB fun m => q₀ * (m + 1) * (m + (a₁ * (c₁ * (3 * m + 2 + 1) ^ c₁ + 1) + a₁ * m + (a₂ * (c₂ * (3 * m + 2 + 1) ^ c₂ + 1) + a₂ * m)) + 1) ^ q₀ :=
    ((PB.const q₀).mul (PB.id'.add (PB.const 1))).mul
      (((PB.id'.add ((((PB.const a₁).mul ((pP c₁).add (PB.const 1))).add ((PB.const a₁).mul PB.id')).add
        (((PB.const a₂).mul ((pP c₂).add (PB.const 1))).add ((PB.const a₂).mul PB.id')))).add (PB.const 1)).pow q₀)
  obtain ⟨q, hq⟩ := pG
  refine ⟨q, fun t n p₁ p₂ hp₁ hp₂ => le_trans ?_ (hq (t + n))⟩
  have m₁ : c₁ * (3 * n + 2 + 1) ^ c₁ ≤ c₁ * (3 * (t + n) + 2 + 1) ^ c₁ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c₁)
  have m₂ : c₂ * (3 * n + 2 + 1) ^ c₂ ≤ c₂ * (3 * (t + n) + 2 + 1) ^ c₂ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c₂)
  have u₁ : a₁ * (p₁ + 1) ≤ a₁ * (c₁ * (3 * (t + n) + 2 + 1) ^ c₁ + 1) := Nat.mul_le_mul_left _ (by omega)
  have u₂ : a₂ * (p₂ + 1) ≤ a₂ * (c₂ * (3 * (t + n) + 2 + 1) ^ c₂ + 1) := Nat.mul_le_mul_left _ (by omega)
  have v₁ : a₁ * t ≤ a₁ * (t + n) := Nat.mul_le_mul_left _ (by omega)
  have v₂ : a₂ * t ≤ a₂ * (t + n) := Nat.mul_le_mul_left _ (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) q₀)
end TwoMachines
