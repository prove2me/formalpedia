-- Prove2me | solution 1 for Printed.poly_absorb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:24:14.168907+00:00
-- url     : https://prove2.me/submissions/a0753857-5715-47f2-a444-bcdffeeb64a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_GroupingProcs
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Mathlib.Tactic
import Definitions.Def_Printed_LevelNetworks
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (A L : ℕ) : ∃ A' : ℕ, ∀ X Y : ℕ, 1 ≤ Y → X ≤ 5 * Y → A * X ^ A + L * X ≤ A' * Y ^ A' := by
  obtain ⟨A', hA'⟩ : ∃ A', A' = A * 5 ^ A + 5 * L + A + 1 := ⟨_, rfl⟩
  refine ⟨A', fun X Y hY hX => ?_⟩
  have h1 : X ^ A ≤ 5 ^ A * Y ^ A' := by
    calc X ^ A ≤ (5 * Y) ^ A := Nat.pow_le_pow_left hX A
      _ = 5 ^ A * Y ^ A := Nat.mul_pow 5 Y A
      _ ≤ 5 ^ A * Y ^ A' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY (by omega))
  have h2 : X ≤ 5 * Y ^ A' := hX.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) Y))
  calc A * X ^ A + L * X ≤ A * (5 ^ A * Y ^ A') + L * (5 * Y ^ A') := Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (A * 5 ^ A + 5 * L) * Y ^ A' := by ring
    _ ≤ A' * Y ^ A' := Nat.mul_le_mul_right _ (by omega)
end Printed
