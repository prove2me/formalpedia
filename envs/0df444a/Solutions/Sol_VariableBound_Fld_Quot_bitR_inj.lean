-- Prove2me | solution 1 for VariableBound.Fld.Quot.bitR_inj
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:37:33.066651+00:00
-- url     : https://prove2.me/submissions/f19d4b41-0dcb-44b9-9586-1c1871a46ce5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Alg
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial

theorem solution {b b' : Bool} (h : bitR (ZMod 2) b = bitR (ZMod 2) b') : b = b' := by
  cases b <;> cases b'
  · rfl
  · exact ((by decide : (0 : ZMod 2) ≠ 1) h).elim
  · exact ((by decide : (1 : ZMod 2) ≠ 0) h).elim
  · rfl
