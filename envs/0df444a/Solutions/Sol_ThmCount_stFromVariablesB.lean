-- Prove2me | solution 1 for ThmCount.stFromVariablesB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:25:50.638999+00:00
-- url     : https://prove2.me/submissions/d0e675d8-e17c-4d11-8048-71b11611dfb3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_FrontEnd
import Definitions.Def_ThmCount_Rates
import Definitions.Def_Wrap_Main
import Mathlib.Tactic
import Definitions.Def_ThmCount_Main
import Theorems.Thm_ThmCount_wrapper_counts
import Theorems.Thm_ThmCount_time_cast
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_ThmCount_stInputLength
import Theorems.Thm_ThmCount_stRates


set_option autoImplicit false
section
section
open ThmCount
open Turing Groundwork PaperSentences
namespace ThmCount
theorem _root_.solution : StFromVariablesB := fun M C hM pre hpre N q hW => by
  obtain ⟨a, d, hl⟩ := stInputLength
  obtain ⟨C', hC'⟩ := stRates C q a d
  exact ⟨C', _, wrapper_counts hl hM hpre hW, fun n hn => (time_cast C q a d n).trans (hC' n hn)⟩
end ThmCount
