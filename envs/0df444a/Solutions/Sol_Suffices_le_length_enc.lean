-- Prove2me | solution 1 for Suffices.le_length_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:29:51.582873+00:00
-- url     : https://prove2.me/submissions/720fb3d6-f706-4a3f-928d-bfbef95f84a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Sizes
import Definitions.Def_Exits_Runs
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_Suffices_Loop
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
open Groundwork.Sparsify (leaves)
namespace Suffices
theorem _root_.solution {n : ℕ} (φ : Sat3.CNF n) : n ≤ (Sat3.enc φ).length + 1 ∧ φ.length ≤ (Sat3.enc φ).length + 1 := by
  have hlen := Decode.length_enc φ
  have := Nat.le_mul_of_pos_right φ.length (show 0 < 3 * (Nat.log2 (2 * n) + 1) by omega)
  omega
end Suffices
