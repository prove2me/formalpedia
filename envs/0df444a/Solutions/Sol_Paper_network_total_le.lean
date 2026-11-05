-- Prove2me | solution 1 for Paper.network_total_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:44:12.130236+00:00
-- url     : https://prove2.me/submissions/be4d0253-acbb-43f6-af6d-ecbccf962a9a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_StepMachines_Math_SatArith
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_StepMachines_Prog_SidePresents
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_StepMachines_Math_SparsifyList
import Definitions.Def_ToTuring_Poly_Count
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_Paper_SecProof_Proof
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_U_wordNet
import Theorems.Thm_Groundwork_SatNet_U_net_le
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Paper
open Groundwork Groundwork.Prog Finset
namespace Paper
theorem _root_.solution {g : ℕ} (hg : 0 < g) (Φ : Formula) : (networkOf g Φ).U ≤ 6 * Φ.length := by
  rw [Count.U_wordNet hg]
  exact SatNet.U_net_le
end Paper
