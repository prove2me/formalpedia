-- Prove2me | solution 1 for Paper.groupedLength_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:31:57.754119+00:00
-- url     : https://prove2.me/submissions/2b51904e-1a31-4f10-a61c-adbed1b98b8f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Model
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_Brute
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_Paper_SecNetworks_Networks
import Theorems.Thm_Groundwork_Colouring_beta_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_RebalanceArith_beta_le
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Paper
open Groundwork Groundwork.Prog Finset
variable {g K : ℕ}
namespace Paper
theorem _root_.solution (K g U P : ℕ) : K ^ 3 * groupedLength K g U P ≤ K ^ 3 + K * U + g * P := Colouring.beta_le K g U P
end Paper
