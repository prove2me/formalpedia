-- Prove2me | solution 1 for ThmCount.sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:59:10.759205+00:00
-- url     : https://prove2.me/submissions/a42aa867-b0fa-4052-8748-49e5d0947dd0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_Rates
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_StepSparsify
import Definitions.Def_SparsificationLemma_Sketch
import Mathlib.Tactic
import Definitions.Def_ThmCount_MEps
import Theorems.Thm_Groundwork_PolyT_div_pow
attribute [local fun_prop] Groundwork.PolyT.div_pow



set_option autoImplicit false
section
section
open ThmCount
open PaperSentences
namespace ThmCount
theorem _root_.solution {e : ℝ} (e0 : 0 < e) (lam : ℝ) : e ^ (-2 : ℝ) * lam ^ 2 = (lam / e) ^ 2 := by
  rw [Real.rpow_neg e0.le, Real.rpow_two, div_pow]
  ring
end ThmCount
