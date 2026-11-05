-- Prove2me | solution 1 for PaddedDescent.F.Arith.Kseq_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:18:37.547486+00:00
-- url     : https://prove2.me/submissions/40767c22-70ed-4cd9-9609-ce8647bccfc5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
import Theorems.Thm_PaddedDescent_Kseq_strictMono


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
namespace PaddedDescent.F.Arith
theorem _root_.solution {i j : ℕ} (h : i ≤ j) : Kseq i ≤ Kseq j := Kseq_strictMono.monotone h
end PaddedDescent.F.Arith
