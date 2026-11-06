-- Prove2me | solution 1 for ThmCount.stRemarkTime_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:42:10.380943+00:00
-- url     : https://prove2.me/submissions/955e266b-c834-4d2f-ace6-4f93d1d94974

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
import Theorems.Thm_ThmCount_stCanBeWrappedAndEveryWrapperCounts
import Theorems.Thm_ClauseBound_Alg_End_time_le
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_ThmCount_remark_rate
import Theorems.Thm_ThmCount_stInputLength
import Theorems.Thm_ThmCount_time_le


set_option autoImplicit false
section
section
open ThmCount
open Turing Groundwork PaperSentences
namespace ThmCount
theorem _root_.solution (h : MainTheoremForms.ThmVariablesB) : StRemarkTime := by
  obtain ⟨M, C, hfin, hM⟩ := h
  obtain ⟨⟨pre, N, q, -, hm, hf, hW⟩, -⟩ := stCanBeWrappedAndEveryWrapperCounts M C hfin hM
  obtain ⟨a, d, hl⟩ := stInputLength
  obtain ⟨K, hK⟩ := time_le C q a d
  exact ⟨K, N, _, hf, wrapper_counts hl hM hm hW, fun n hn => (time_cast C q a d n).trans (hK n _ (remark_rate hn).1 (remark_rate hn).2)⟩
end ThmCount
