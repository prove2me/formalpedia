-- Prove2me | solution 1 for VariableBound.lemFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:08:31.306818+00:00
-- url     : https://prove2.me/submissions/8d1f5dab-9834-4da8-9025-c22ced8774b1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main
import Theorems.Thm_VariableBound_Family_card_Om
import Theorems.Thm_VariableBound_Family_card_Om_lt
import Theorems.Thm_VariableBound_Family_part_a
import Theorems.Thm_VariableBound_Family_part_b
import Theorems.Thm_VariableBound_Family_part_c

set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open Family
namespace VariableBound
theorem _root_.solution : AppVariables.LemFamily := by
  intro F _ _ _ _ m s a bits ϑ ha1 hvm h16 h32
  have hm : 1 ≤ m := Nat.one_le_two_pow.trans hvm
  have ha : a - 1 ≤ s := by
    have h : 2 ^ a < 2 ^ s := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h
    omega
  refine ⟨?_, card_Om_lt bits ϑ a h32, ?_, part_b bits ϑ a ha1 ha hm, part_c bits ϑ a ha1 ha hm h16⟩
  · have h1 := card_Om bits ϑ a ha1 ha hm
    have h2 : 0 < Fintype.card F ^ 4 := pow_pos Fintype.card_pos 4
    omega
  · intro u hu
    rw [Fintype.card_fin]
    exact part_a bits ϑ a u hu
end VariableBound
