-- Prove2me | solution 1 for VariableBound.Net.SizeSmall.stSmall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:22:12.894803+00:00
-- url     : https://prove2.me/submissions/81e7c4b9-02ac-490d-8d3e-62ed39865ffa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_SizeP
import Definitions.Def_VariableBound_Net_SizeSmall
import Theorems.Thm_VariableBound_Net_SizeSmall_length_tch_le
import Theorems.Thm_VariableBound_Net_SizeSmall_abs_WD_le
import Theorems.Thm_VariableBound_Net_SizeSmall_U_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Mark_Deg_length_tch_le
import Theorems.Thm_VariableBound_Net_SizeB_abs_WD_le
import Theorems.Thm_VariableBound_Net_SizeP_length_tch_le
import Theorems.Thm_VariableBound_Net_SizeP_sized_netDN


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeSmall
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (qv occ)
variable {k g n Δ : ℕ}
namespace VariableBound.Net.SizeSmall
theorem _root_.solution : StSmall := by
  intro k g n Δ nb M ψ fl y hg hW hΔ hm _
  refine ⟨SizeP.sized_netDN (fun a _ => ?_) (fun a _ => ?_) fun a _ z => abs_WD_le ψ y fl a z, ?_⟩
  · have := length_tch_le hg hW hΔ a
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · have := length_tch_le hg hW hΔ a
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · exact (U_le hW y fl).trans (Nat.mul_le_mul_left _ hm)
end VariableBound.Net.SizeSmall
