-- Prove2me | solution 1 for PaddedDescent.decidesTM_of_padded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:41:48.966818+00:00
-- url     : https://prove2.me/submissions/2d48ef66-3c69-4bac-adb0-612d9c1d5bfe

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
import Theorems.Thm_PaddedDescent_exists_tm_padded
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}
namespace PaddedDescent
theorem _root_.solution (he : PolyT e) (hA : PolyT A) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ E : ℕ → ℕ,
        (∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
          e (enc φ) ≤ E n ∧ (A (enc φ, pad (e (enc φ))) = true ↔ Satisfiable φ)) →
        DecidesTM N fun n => q * (25 * (n + 2) ^ 4 + 2 ^ E n) ^ q := by
  obtain ⟨N, q, hfin, hN⟩ := exists_tm_padded he hA
  refine ⟨N, q, hfin, fun E h n φ h3 => ?_⟩
  obtain ⟨hE, hb⟩ := h n φ h3
  obtain ⟨ev⟩ := hN (enc φ)
  have h5 : (enc φ).length + 1 ≤ 25 * (n + 2) ^ 4 := Groundwork.Decode.length_enc_succ_le h3
  have h6 : 2 ^ e (enc φ) ≤ 2 ^ E n := Nat.pow_le_pow_right (by norm_num) hE
  have hle : q * ((enc φ).length + 2 ^ e (enc φ) + 1) ^ q ≤ q * (25 * (n + 2) ^ 4 + 2 ^ E n) ^ q :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) q)
  exact ⟨_, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩⟩
end PaddedDescent
