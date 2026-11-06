-- Prove2me | solution 1 for Printed.stCountCost_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:53:06.153929+00:00
-- url     : https://prove2.me/submissions/f19e90e9-108a-4416-9edb-1608d6a5b3d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
import Theorems.Thm_Printed_onFormula_poly
import Theorems.Thm_Printed_onFormula
import Theorems.Thm_Printed_cost_of_bound
import Theorems.Thm_Printed_cost_with_first_line
import Theorems.Thm_Printed_firstLine_poly
import Theorems.Thm_Eight_ViaGrouping_Correct_onFormula
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Paper_levelK_ge
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines
namespace Printed
theorem _root_.solution (hC : StClique) (hG : StGroupingTied) (hGp : StGroupingPoly) (hOn : StOnProcedures) : StCountCost := by
  intro δ' ℓ hδ' h1 hK hE
  obtain ⟨hp, Cc, hA⟩ := hC ℓ
  have hK2 : 2 ≤ levelK ℓ := (by norm_num : 2 ≤ 64).trans (levelK_ge ℓ)
  obtain ⟨C₁, hC₁⟩ := hG (levelK ℓ) (δ' / 12) (CLIQUE ℓ) Cc hK2 (by positivity) (hA.mono hE)
  have hC₁' : ComputesNetworks (NETWORK ℓ) C₁ (levelG ℓ) (levelK ℓ) (δ' / 12) := hC₁
  have hg : 0 < levelG ℓ := Nat.mul_pos (by norm_num) (pow_pos (by omega) 8)
  obtain ⟨A, hA'⟩ := cost_of_bound hδ' h1 hg hK (onFormula hOn hg 3 hC₁')
  exact ⟨firstLine_poly (onFormula_poly _ 3 _ (hGp _ _ _ hp)), A + 4, cost_with_first_line hA'⟩
end Printed
