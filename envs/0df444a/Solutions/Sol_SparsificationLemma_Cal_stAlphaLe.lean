-- Prove2me | solution 1 for SparsificationLemma.Cal.stAlphaLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:36:54.132407+00:00
-- url     : https://prove2.me/submissions/d3f86b2a-aedd-4fec-8417-89d7edf402f8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Theorems.Thm_SparsificationLemma_Cal_alphaC_le_sqrt
import Theorems.Thm_SparsificationLemma_Cal_sqrt_xC_le
import Theorems.Thm_SparsificationLemma_Cal_div_sqrt_le_cube
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution : StAlphaLe := fun k _ hk h0 h1 =>
  (alphaC_le_sqrt hk h0 h1).trans ((sqrt_xC_le hk h0).trans (div_sqrt_le_cube k h0 h1))
end SparsificationLemma.Cal
