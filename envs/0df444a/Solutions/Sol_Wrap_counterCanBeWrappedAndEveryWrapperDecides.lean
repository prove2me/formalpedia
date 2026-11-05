-- Prove2me | solution 1 for Wrap.counterCanBeWrappedAndEveryWrapperDecides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:08:23.562065+00:00
-- url     : https://prove2.me/submissions/a9bbc5ef-04df-46e4-a69c-40104f24d430

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
import Theorems.Thm_Wrap_everyMachineCanBeWrapped
import Theorems.Thm_Wrap_everyWrapperOfACounterDecidesEveryDelta
import Theorems.Thm_Wrap_everyWrapperOfACounterDecidesAtRateInN
import Theorems.Thm_Wrap_lastStepsArePolynomialTime
import Theorems.Thm_Wrap_frontEndExists


set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork
open scoped NNReal
namespace Wrap
theorem _root_.solution : CounterCanBeWrappedAndEveryWrapperDecides := fun M C hfin hM =>
  let ⟨pre, hpre⟩ := frontEndExists
  let ⟨N, q, hN, hW⟩ := everyMachineCanBeWrapped M hfin pre someBit hpre.1 lastStepsArePolynomialTime.2
  ⟨⟨pre, N, q, hpre, hN, hW⟩, fun pre' hpre' N' q' hW' =>
    ⟨everyWrapperOfACounterDecidesEveryDelta pre' hpre' M C hM N' q' hW', everyWrapperOfACounterDecidesAtRateInN pre' hpre' M C hM N' q' hW'⟩⟩
end Wrap
