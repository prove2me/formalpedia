-- Prove2me | solution 1 for PaddedDescent.F.Table.stT3b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:16.926176+00:00
-- url     : https://prove2.me/submissions/3ad23c97-3e2e-40de-8830-cbecf56e5ba6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_PaddedDescent_F_Table
import Theorems.Thm_PaddedDescent_F_Table_len_ints_le
import Theorems.Thm_PaddedDescent_F_Table_len_rows_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_len_units
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Table
open Groundwork Groundwork.Prog Finset
namespace PaddedDescent.F.Table
theorem _root_.solution : StT3b := by
  intro K Λ B I h
  obtain ⟨lu, T⟩ := I
  have h1 : len T ≤ T.length * (2 ^ ((K - 1) * lu.length) * (3 * B + 10) + 4) + 2 :=
    len_rows_le T fun r hr => by
      have := len_ints_le r (h.abs_le r hr)
      rwa [h.row_len r hr] at this
  have h2 : T.length = K := h.rows
  have h3 : lu.length ≤ Λ := h.lam_le
  have h4 : 2 ^ ((K - 1) * lu.length) ≤ 2 ^ ((K - 1) * Λ) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h3)
  have h5 : K * (2 ^ ((K - 1) * lu.length) * (3 * B + 10) + 4) ≤ K * (2 ^ ((K - 1) * Λ) * (3 * B + 10) + 4) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ h4) _)
  rw [h2] at h1
  rw [len_pair, len_units]
  unfold instLen
  omega
end PaddedDescent.F.Table
