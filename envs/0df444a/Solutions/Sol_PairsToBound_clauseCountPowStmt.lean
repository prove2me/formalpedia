-- Prove2me | solution 1 for PairsToBound.clauseCountPowStmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:58:58.358912+00:00
-- url     : https://prove2.me/submissions/7bc2a050-deb0-466c-a7ec-5292a03a29f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Width
import Theorems.Thm_SparsificationLemma_StepSparsify_pow_le


set_option autoImplicit false
section
section
open PairsToBound
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution : ClauseCountPowStmt := fun k _ hn => SparsificationLemma.StepSparsify.pow_le hn k
end PairsToBound
