-- Prove2me | solution 1 for Wrap.oneMachineEveryDeltaAndETHFails_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:42:32.856905+00:00
-- url     : https://prove2.me/submissions/ca36d81b-f4fe-4b41-8e28-0ca3144be7ed

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
import Theorems.Thm_WidthThree_ethFailsWording_of_subexpTM
import Theorems.Thm_WidthThree_ethFails_of_subexpTM
import Theorems.Thm_WidthThree_everyDeltaAMachineWording_of_subexpTM
import Theorems.Thm_WidthThree_everyDeltaAMachine_of_subexpTM


set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork
open scoped NNReal
namespace Wrap
theorem _root_.solution {N : TM2ComputableAux Bool Bool} (hN : ∀ i, Finite (N.tm.Γ i)) (h : DecidesEveryDelta N) : OneMachineEveryDeltaAndETHFails :=
  have hs : Sat3.SubexpTM := ⟨N, hN, h⟩
  ⟨hs, WidthThree.everyDeltaAMachine_of_subexpTM hs, WidthThree.ethFails_of_subexpTM hs, WidthThree.everyDeltaAMachineWording_of_subexpTM hs, WidthThree.ethFailsWording_of_subexpTM hs⟩
end Wrap
