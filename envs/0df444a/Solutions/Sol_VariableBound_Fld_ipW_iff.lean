-- Prove2me | solution 1 for VariableBound.Fld.ipW_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:38:29.568191+00:00
-- url     : https://prove2.me/submissions/b30a445e-f7df-4312-b11c-a24042fc02cf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Search
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Field_Family
import Theorems.Thm_VariableBound_Fld_sum_bitR_mul

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset Polynomial
namespace VariableBound.Fld
theorem _root_.solution {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    ipW x y = true ↔ AppVariables.ip (fun i : Fin n => bitR (ZMod 2) (x.getD i.val false)) (fun i : Fin n => bitR (ZMod 2) (y.getD i.val false)) = 1 := by
  rw [AppVariables.ip, sum_bitR_mul n x y hx hy, ipW, decide_eq_true_iff, ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]
end VariableBound.Fld
