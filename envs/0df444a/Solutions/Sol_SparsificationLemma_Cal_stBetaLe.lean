-- Prove2me | solution 1 for SparsificationLemma.Cal.stBetaLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:39.29034+00:00
-- url     : https://prove2.me/submissions/426c6151-790f-4ca6-816d-460ec45a046e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta
import Theorems.Thm_SparsificationLemma_Cal_stBetaCat
import Theorems.Thm_SparsificationLemma_Cal_stCatLe
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset
namespace SparsificationLemma.Cal
theorem _root_.solution : StBetaLe := by
  intro α c
  rw [stBetaCat]
  calc 2 * (8 * α) ^ c * catalan c ≤ 2 * (8 * α) ^ c * 4 ^ c := Nat.mul_le_mul_left _ (stCatLe c)
    _ = 2 * (32 * α) ^ c := by rw [Nat.mul_assoc, ← mul_pow]; congr 2; ring
end SparsificationLemma.Cal
