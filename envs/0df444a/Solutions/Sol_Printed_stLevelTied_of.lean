-- Prove2me | solution 1 for Printed.stLevelTied_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:00:31.995655+00:00
-- url     : https://prove2.me/submissions/99701591-15aa-428b-be84-b4146956fb0f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelNetworks
import Definitions.Def_Eight_ViaGrouping_Level
import Mathlib.Tactic
import Definitions.Def_Printed_LevelCost
import Theorems.Thm_Printed_levelMachine_achieves_of

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (hA : StAskServes) (hV : StCliqueValue) (hG : StGroupingTied) (hO : StOnProcedures) : StLevelTied := by
  intro K e M Cc hK h0 hM
  obtain ⟨C₁, hC⟩ := hG K e M Cc hK h0 hM
  have hg : K ≤ 3 * K ^ 8 := by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega
  rw [sq]
  exact levelMachine_achieves_of hA hV hO hK hg h0 hC
end Printed
