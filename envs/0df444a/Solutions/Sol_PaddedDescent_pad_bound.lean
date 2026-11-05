-- Prove2me | solution 1 for PaddedDescent.pad_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:34:00.578721+00:00
-- url     : https://prove2.me/submissions/6ef42bba-a048-4fa5-8b44-999ad3c3b024

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_PaddedDescent_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_PaddedDescent_Pad

set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}
namespace PaddedDescent
theorem _root_.solution (q l e : ℕ) : q * (e + 1 + 1) * (l + (2 * l + 2 * 2 ^ e + 3) + 1) ^ q ≤
    (q * 4 ^ (q + 1) + (q + 1)) * (l + 2 ^ e + 1) ^ (q * 4 ^ (q + 1) + (q + 1)) := by
  obtain ⟨m, hm⟩ : ∃ m, m = l + 2 ^ e + 1 := ⟨_, rfl⟩
  have h0 : e < 2 ^ e := Nat.lt_two_pow_self
  have h1 : e + 1 + 1 ≤ 4 * m := by omega
  have h2 : l + (2 * l + 2 * 2 ^ e + 3) + 1 ≤ 4 * m := by omega
  have hm1 : 1 ≤ m := by omega
  rw [← hm]
  calc q * (e + 1 + 1) * (l + (2 * l + 2 * 2 ^ e + 3) + 1) ^ q ≤ q * (4 * m) * (4 * m) ^ q :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (Nat.pow_le_pow_left h2 q)
    _ = q * 4 ^ (q + 1) * m ^ (q + 1) := by rw [Nat.mul_assoc, ← pow_succ', Nat.mul_pow, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right hm1 (Nat.le_add_left _ _))
end PaddedDescent
