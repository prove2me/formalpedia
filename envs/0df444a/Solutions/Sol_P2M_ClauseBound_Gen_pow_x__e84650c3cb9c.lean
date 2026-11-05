-- Prove2me | solution 1 for P2M_ClauseBound_Gen_pow_x__e84650c3cb9c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:54:51.828522+00:00
-- url     : https://prove2.me/submissions/fae23aec-7f86-40fa-b215-a130e2cfeace

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Levels.Gen
namespace ClauseBound.Gen
theorem _root_.solution (x₀ : ℕ) (hx : 18 ≤ x₀) : 2 ^ 10 * (3 * x₀ + 6) ≤ 2 ^ x₀ := by
  induction x₀, hx using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega
end ClauseBound.Gen
