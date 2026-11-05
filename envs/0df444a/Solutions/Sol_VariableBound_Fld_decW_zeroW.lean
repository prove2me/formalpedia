-- Prove2me | solution 1 for VariableBound.Fld.decW_zeroW
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:32:54.651061+00:00
-- url     : https://prove2.me/submissions/d38b237a-b4c5-4bc0-bbc5-f393434c209c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Ring
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial

private lemma decR_zeroW_aux {R : Type} [CommRing R] (r : R) (g : List Bool) :
    decR r (zeroW g) = 0 := by
  induction g with
  | nil => rfl
  | cons b g ih =>
    have e : zeroW (b :: g) = false :: zeroW g := rfl
    rw [e, decR, ih]
    simp [bitR]

theorem solution (g : List Bool) : decW g (zeroW g) = 0 := decR_zeroW_aux _ _
