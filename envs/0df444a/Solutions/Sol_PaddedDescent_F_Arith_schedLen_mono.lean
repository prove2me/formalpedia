-- Prove2me | solution 1 for PaddedDescent.F.Arith.schedLen_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:03:05.980925+00:00
-- url     : https://prove2.me/submissions/912c92be-7846-40db-a11b-652834a3eeb7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithCol
import Definitions.Def_PaddedDescent_F_ArithSched
import Theorems.Thm_PaddedDescent_F_Arith_Lseq_mono
import Theorems.Thm_PaddedDescent_Kseq_strictMono


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork PaddedDescent.F.Lists
open PaddedDescent.F.Arith
namespace PaddedDescent.F.Arith
theorem _root_.solution {i j : ℕ} (h : i ≤ j) : schedLen i ≤ schedLen j := by
  have h1 := Kseq_strictMono.monotone h
  have h2 := Lseq_mono h
  unfold schedLen
  gcongr
end PaddedDescent.F.Arith
