-- Prove2me | solution 1 for ThmCount.stCanBeWrappedAndEveryWrapperCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:29:19.873069+00:00
-- url     : https://prove2.me/submissions/a8fab214-1a0c-49e0-812c-67cfb8e46b4e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_FrontEnd
import Definitions.Def_ThmCount_Rates
import Definitions.Def_Wrap_Main
import Mathlib.Tactic
import Definitions.Def_ThmCount_Main
import Theorems.Thm_ThmCount_stFromVariablesB
import Theorems.Thm_ThmCount_stFrontEnd
import Theorems.Thm_ThmCount_stLastStep
import Theorems.Thm_Wrap_everyMachineCanBeWrapped


set_option autoImplicit false
section
section
open ThmCount
open Turing Groundwork PaperSentences
namespace ThmCount
theorem _root_.solution : StCanBeWrappedAndEveryWrapperCounts := fun M C hfin hM => by
  refine ⟨?_, fun pre hpre N q hW => stFromVariablesB M C hM pre hpre N q hW⟩
  obtain ⟨pre, hp, hm⟩ := stFrontEnd
  obtain ⟨N, q, hf, hW⟩ := Wrap.everyMachineCanBeWrapped M hfin pre dropFour hp stLastStep
  exact ⟨pre, N, q, hp, hm, hf, hW⟩
end ThmCount
