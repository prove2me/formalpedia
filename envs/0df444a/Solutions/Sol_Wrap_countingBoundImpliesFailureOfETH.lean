-- Prove2me | solution 1 for Wrap.countingBoundImpliesFailureOfETH
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:46.105736+00:00
-- url     : https://prove2.me/submissions/39e03875-62f3-4f80-b530-7d36aa633c7c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_Wrap_Sim
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_WidthThree_Rates
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_Wrap_Main
import Theorems.Thm_Wrap_counterCanBeWrappedAndEveryWrapperDecides
import Theorems.Thm_Wrap_oneMachineEveryDeltaAndETHFails_of

set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork
open scoped NNReal
namespace Wrap
theorem _root_.solution : CountingBoundImpliesFailureOfETH := fun ⟨M, C, hfin, hM⟩ =>
  let ⟨⟨pre, N, q, hpre, hN, hW⟩, hall⟩ := counterCanBeWrappedAndEveryWrapperDecides M C hfin hM
  oneMachineEveryDeltaAndETHFails_of hN (hall pre hpre.2 N q hW).1
end Wrap
