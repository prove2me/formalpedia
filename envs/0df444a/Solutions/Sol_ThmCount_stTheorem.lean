-- Prove2me | solution 1 for ThmCount.stTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:44:25.347203+00:00
-- url     : https://prove2.me/submissions/37d9c3c1-1a1f-431b-b2a0-d377b8095037

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_FrontEnd
import Definitions.Def_ThmCount_Rates
import Definitions.Def_Wrap_Main
import Mathlib.Tactic
import Definitions.Def_ThmCount_Main
import Theorems.Thm_ThmCount_stCanBeWrappedAndEveryWrapperCounts

set_option autoImplicit false
section
section
open ThmCount
open Turing Groundwork PaperSentences
namespace ThmCount
theorem _root_.solution : StTheorem := fun h => by
  obtain ⟨M, C, hfin, hM⟩ := h
  obtain ⟨⟨pre, N, q, -, hm, hf, hW⟩, h2⟩ := stCanBeWrappedAndEveryWrapperCounts M C hfin hM
  obtain ⟨C', t, ht, hle⟩ := h2 pre hm N q hW
  exact ⟨C', N, t, hf, ht, hle⟩
end ThmCount
