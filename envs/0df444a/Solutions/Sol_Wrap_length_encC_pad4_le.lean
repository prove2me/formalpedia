-- Prove2me | solution 1 for Wrap.length_encC_pad4_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:16:09.261846+00:00
-- url     : https://prove2.me/submissions/b53fa3d0-a0e2-4287-a4af-55e124b7466e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_FrontEnd
import Theorems.Thm_Wrap_pad4KeepsSatAndMeetsSideConditions
import Theorems.Thm_Wrap_length_encC
import Theorems.Thm_Groundwork_Decode_bitLen_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Sat3_Is3CNF_length_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Wrap
open Groundwork Groundwork.Decode
namespace Wrap
theorem _root_.solution : ∃ a d : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ →
    (MainTheoremForms.encC 3 (pad4 φ)).length ≤ a * (n + 2) ^ d ∧ (Sat3.enc φ).length ≤ a * (n + 2) ^ d := by
  refine ⟨100, 4, fun n φ hφ => ⟨?_, ?_⟩⟩
  · have hm : (pad4 φ).length = φ.length + 4 := (pad4KeepsSatAndMeetsSideConditions n φ hφ).2.1
    have h1 : φ.length ≤ (2 * n + 1) ^ 3 := hφ.length_le
    have h2 : Nat.log2 (2 * (n + 4)) + 1 ≤ n + 4 + 1 := bitLen_le (n + 4)
    rw [length_encC, hm]
    generalize Nat.log2 (2 * (n + 4)) + 1 = w at h2 ⊢
    have h3 : (φ.length + 4) * (3 * w) ≤ ((2 * n + 1) ^ 3 + 4) * (3 * (n + 5)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : 3 + (n + 5) + 2 + ((2 * n + 1) ^ 3 + 4) * (3 * (n + 5)) ≤ 100 * (n + 2) ^ 4 := by nlinarith [sq_nonneg n]
    omega
  · have := length_enc_succ_le hφ
    have : 0 ≤ (n + 2) ^ 4 := Nat.zero_le _
    omega
end Wrap
