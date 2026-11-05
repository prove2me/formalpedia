-- Prove2me | solution 1 for ThmCount.time_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:10.661466+00:00
-- url     : https://prove2.me/submissions/aa4b9bf2-1934-48cb-a574-d56d190008bb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_FrontEnd
import Definitions.Def_ThmCount_Rates
import Definitions.Def_Wrap_Main
import Mathlib.Tactic
import Definitions.Def_ThmCount_Main
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d


set_option autoImplicit false
section
section
open ThmCount
open Turing Groundwork PaperSentences
namespace ThmCount
theorem _root_.solution (C q a d n : ℕ) : ((q * (MainTheoremForms.timeN C 3 (n + 4) + a * (n + 2) ^ d + 1) ^ q : ℕ) : ℝ) ≤
    (q : ℝ) * ((2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) + (a : ℝ) * ((n : ℝ) + 2) ^ d + 1) ^ q := by
  have h : (MainTheoremForms.timeN C 3 (n + 4) : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) := Nat.floor_le (by positivity)
  push_cast
  gcongr
end ThmCount
