-- Prove2me | solution 1 for P2M_Groundwork_Prog_Count_wordNet___eq_78331b67b704
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:25:00.360203+00:00
-- url     : https://prove2.me/submissions/edf091dc-bfa7-4886-9012-d830e71d1322

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_all_links_iff
import Theorems.Thm_Groundwork_Prog_Count_boole_congr
import Theorems.Thm_P2M_Groundwork_Prog_Count_wordNet___lt_709805682ec2
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_P2M_Groundwork_SatNet___of_lt_d32e7cdb1e61
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) {a b : Fin g} (h : a < b) (z z' : List Bool) :
    (wordNet g k φ).Ψ a b z z' = (net φ g (mu g φ) k).Ψ a b (bits z) (bits z') := by
  rw [wordNet_Ψ_lt h, SatNet.Ψ_of_lt h]
  refine boole_congr ?_
  rw [all_links_iff hg hm a b fun r r' => z.getD r false == z'.getD r' false]
  simp only [beq_iff_eq, bits]
end Groundwork.Prog.Count
