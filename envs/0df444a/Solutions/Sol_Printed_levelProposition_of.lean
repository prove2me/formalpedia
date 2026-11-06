-- Prove2me | solution 1 for Printed.levelProposition_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:16:27.536006+00:00
-- url     : https://prove2.me/submissions/a8bdf08a-9674-4535-aaf3-45a8dded6a4d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelCost
import Definitions.Def_Eight_SecPseudocode_Levels
import Mathlib.Tactic
import Definitions.Def_Printed_LevelSentences

set_option autoImplicit false
section
section
open Printed
open Eight Paper QueryMachines
namespace Printed
theorem _root_.solution (hT : StLevelTied) (hP : StLevelPoly) : LevelProposition := by
  intro K e hA
  obtain ⟨hK, h0, M, Cc, hp, hM⟩ := hA
  obtain ⟨Cc', h⟩ := hT K e M Cc hK h0 hM
  refine ⟨?_, ?_, levelMachine K (3 * K ^ 8) M, Cc', hP K (3 * K ^ 8) M hp, h⟩
  · have h1 : 1 ≤ K ^ 8 := Nat.one_le_pow _ _ (by omega)
    have h2 : 3 * K ^ 8 ≤ (3 * K ^ 8) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  · have hρ : (0 : ℝ) < rho := by unfold rho; norm_num
    positivity
end Printed
