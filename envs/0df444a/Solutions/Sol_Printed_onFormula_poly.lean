-- Prove2me | solution 1 for Printed.onFormula_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:38:27.903202+00:00
-- url     : https://prove2.me/submissions/861cb60e-08dd-4129-9892-4867c5b93a89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
import Theorems.Thm_Printed_formulaProcs_keeps
import Theorems.Thm_Eight_ViaGrouping_satProcs_keepsP
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Printed_networkOnSteps_poly
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines
namespace Printed
theorem _root_.solution (g k : ℕ) (NM : NetMachine) (hN : NM.PolyTimeSteps) : Nonempty (IsPolyT (networkOnSteps g NM (formulaProcs g k))) :=
  networkOnSteps_poly g NM _ hN (formulaProcs_keeps g k) (satProcs_keepsP g k).P (Unary.const 1)
end Printed
