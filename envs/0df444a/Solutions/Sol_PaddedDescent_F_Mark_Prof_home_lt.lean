-- Prove2me | solution 1 for PaddedDescent.F.Mark.Prof.home_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:17.205985+00:00
-- url     : https://prove2.me/submissions/4f723818-46ff-46f6-90bf-2a6285a03b30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Digits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_PaddedDescent_F_MarkProf

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.Mark.Prof
theorem _root_.solution {g n x : ℕ} (hg : 0 < g) (hx : x < n) : x / qv g n < g := by
  have h1 := Nat.lt_mul_div_succ (n + g - 1) hg
  have h2 : g * ((n + g - 1) / g + 1) = g * ((n + g - 1) / g) + g := by ring
  refine Nat.div_lt_of_lt_mul ?_
  unfold qv
  rw [Nat.mul_comm]
  omega
end PaddedDescent.F.Mark.Prof
