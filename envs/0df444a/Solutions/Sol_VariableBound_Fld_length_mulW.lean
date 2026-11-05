-- Prove2me | solution 1 for VariableBound.Fld.length_mulW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:56:49.147302+00:00
-- url     : https://prove2.me/submissions/2c3e0565-b71c-489c-a376-f6c705094835

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Alg
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Definitions.Def_VariableBound_Field_Ring
import Theorems.Thm_VariableBound_Fld_length_xorW
import Theorems.Thm_VariableBound_Fld_length_zeroW
import Theorems.Thm_VariableBound_Fld_length_mulX

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
variable {R : Type} [CommRing R]
namespace VariableBound.Fld
theorem _root_.solution {g x : List Bool} (hx : x.length = g.length) (y : List Bool) : (mulW g x y).length = g.length := by
  induction y with
  | nil => exact length_zeroW g
  | cons b y ih =>
    have h : mulW g x (b :: y) = if b then xorW x (mulX g (mulW g x y)) else mulX g (mulW g x y) := rfl
    rw [h]
    split
    · rw [length_xorW, length_mulX ih, hx, min_self]
    · exact length_mulX ih
end VariableBound.Fld
