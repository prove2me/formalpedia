-- Prove2me | solution 1 for PaddedDescent.F.Mark.Pi.stPiSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:23:29.855987+00:00
-- url     : https://prove2.me/submissions/beaeeedf-77a1-4106-91c3-76580f393fa2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_vset

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]
namespace PaddedDescent.F.Mark.Pi
theorem _root_.solution : StPiSum := by
  intro w Ls σ
  rw [← sum_vset σ w Ls, sum_filter]
end PaddedDescent.F.Mark.Pi
