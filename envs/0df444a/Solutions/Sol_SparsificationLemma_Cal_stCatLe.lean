-- Prove2me | solution 1 for SparsificationLemma.Cal.stCatLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:15:27.216061+00:00
-- url     : https://prove2.me/submissions/9f616db6-8373-4b50-b762-ca3ef311b72d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset
namespace SparsificationLemma.Cal
theorem _root_.solution : StCatLe := fun j =>
  (Nat.le_mul_of_pos_left _ (Nat.succ_pos j)).trans ((succ_mul_catalan_eq_centralBinom j).le.trans (Nat.centralBinom_le_four_pow j))
end SparsificationLemma.Cal
