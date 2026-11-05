-- Prove2me | solution 2 for VariableBound.Fld.sD_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:24:09.744041+00:00
-- url     : https://prove2.me/submissions/583b9581-30e9-4e00-a2d9-850a360a9921

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
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset
namespace VariableBound.Fld
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) : 2 ^ sD m < 32 * m := by
  have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := 16 * m) (by omega)
  have h2 : 0 < Nat.clog 2 (16 * m) := Nat.clog_pos (by norm_num) (by omega)
  have h3 : 2 ^ sD m = 2 * 2 ^ (Nat.clog 2 (16 * m)).pred := by
    rw [sD, ← pow_succ', Nat.pred_eq_sub_one]; congr 1; omega
  omega
end VariableBound.Fld
