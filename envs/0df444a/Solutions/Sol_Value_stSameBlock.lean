-- Prove2me | solution 1 for Value.stSameBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:46:24.514904+00:00
-- url     : https://prove2.me/submissions/6a3ecbc0-c1de-40c9-811b-12341b938b4d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Eight_SecNetworks_thetaAt_comm
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Value_star_swap
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
namespace Value
theorem _root_.solution : StSameBlock := by
  intro C _ g K Np c hK0 x Λ a b hne
  exact thetaAt_comm Np.toPaperNetwork c hK0 x _ _ hne (star_swap Λ _ _)
end Value
