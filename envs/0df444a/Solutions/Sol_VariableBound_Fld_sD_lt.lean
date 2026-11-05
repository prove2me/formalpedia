-- Prove2me | solution 1 for VariableBound.Fld.sD_lt
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:26:15.19585+00:00
-- url     : https://prove2.me/submissions/d0135674-6cbb-4a6b-a370-138209f6128d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Definitions.Def_VariableBound_Field_Transfer
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset

theorem solution {m : ℕ} (hm : 1 ≤ m) : 2 ^ sD m < 32 * m := by
  have hx : 1 < 16 * m := by omega
  have hpos : 0 < Nat.clog 2 (16 * m) :=
    (Nat.lt_clog_iff_pow_lt (by omega : 1 < 2)).2 (by simpa using hx)
  have hpow : 2 ^ (Nat.clog 2 (16 * m) - 1) < 16 * m :=
    Nat.pow_pred_clog_lt_self (by omega) hx
  calc
    2 ^ sD m = 2 ^ (Nat.clog 2 (16 * m) - 1 + 1) := by
      rw [sD, Nat.sub_add_cancel hpos]
    _ = 2 ^ (Nat.clog 2 (16 * m) - 1) * 2 := by rw [Nat.pow_succ]
    _ < (16 * m) * 2 := (Nat.mul_lt_mul_right (by omega : 0 < 2)).2 hpow
    _ = 32 * m := by omega
