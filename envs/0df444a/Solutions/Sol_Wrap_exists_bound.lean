-- Prove2me | solution 1 for Wrap.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:56:10.610726+00:00
-- url     : https://prove2.me/submissions/113780b4-f593-4ec7-af71-547e6f1cfe46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_Wrap_Sim
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mono_bound
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PB_pow
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}
namespace Wrap
theorem _root_.solution (q₀ a c : ℕ) : ∃ q : ℕ, ∀ t n p : ℕ, p ≤ c * (3 * n + 2 + 1) ^ c →
    q₀ * (t + 1) * (n + (a * (p + 1) + a * t) + 1) ^ q₀ ≤ q * (t + n + 1) ^ q := by
  have pP : PB fun m => c * (3 * m + 2 + 1) ^ c := (PB.mono_bound c).1.comp (((PB.const 3).mul PB.id').add (PB.const 2))
  have pG : PB fun m => q₀ * (m + 1) * (m + (a * (c * (3 * m + 2 + 1) ^ c + 1) + a * m) + 1) ^ q₀ :=
    ((PB.const q₀).mul (PB.id'.add (PB.const 1))).mul
      (((PB.id'.add (((PB.const a).mul (pP.add (PB.const 1))).add ((PB.const a).mul PB.id'))).add (PB.const 1)).pow q₀)
  obtain ⟨q, hq⟩ := pG
  refine ⟨q, fun t n p hp => le_trans ?_ (hq (t + n))⟩
  have h1 : c * (3 * n + 2 + 1) ^ c ≤ c * (3 * (t + n) + 2 + 1) ^ c :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)
  have h2 : a * (p + 1) ≤ a * (c * (3 * (t + n) + 2 + 1) ^ c + 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : a * t ≤ a * (t + n) := Nat.mul_le_mul_left _ (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) q₀)
end Wrap
