-- Prove2me | solution 2 for VariableBound.Fld.bitR_xor
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:24:19.223384+00:00
-- url     : https://prove2.me/submissions/02c2624b-5c08-40e9-a9be-5aaa7738c461

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Alg
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Definitions.Def_VariableBound_Field_Ring
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
variable {R : Type} [CommRing R]

theorem solution (h2 : (2 : R) = 0) (a b : Bool) : bitR R (xor a b) = bitR R a + bitR R b := by
  cases a <;> cases b <;> simp [bitR]
  linear_combination -h2
