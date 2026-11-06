-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.cand_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:13:10.36402+00:00
-- url     : https://prove2.me/submissions/b7664221-6ccc-4abd-9406-0a93422c3c28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_CountedToPadded_Pick
import Theorems.Thm_QueryMachines_Bridge_Proof_eq_unary
import Theorems.Thm_QueryMachines_Bridge_Proof_take_unary
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {K : ℕ → ℕ} {kf : U × U → Option U} (hk : ComputesLevels K kf) (b : U) {l : ℕ} (h : l ≤ b.length) :
    cand kf b l = if K l ≤ b.length then some (unary l, (unary l, unary (K l))) else none := by
  unfold cand
  rw [take_unary b h]
  conv_lhs => rw [eq_unary b]
  rw [hk.2 l b.length]
  split <;> rfl
end QueryMachines.Bridge.Proof
