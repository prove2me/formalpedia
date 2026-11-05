-- Prove2me | solution 1 for QueryMachines.Tower.wfStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:53:01.283435+00:00
-- url     : https://prove2.me/submissions/71f256cc-14f9-4a27-a2d9-9753c1280e90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_Tower_Kernel
import Theorems.Thm_QueryMachines_stWithinRules


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Q A α β : Type} {M : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {s : M.σ} {b : β} {S S' T T' : ℕ}
namespace QueryMachines.Tower
theorem _root_.solution (h1 : M.out s = none) (h2 : M.ask s = none) (h3 : size s ≤ S) (h : M.WithinFrom O w (M.step s) T S b) : M.WithinFrom O w s (T + 1) S b :=
  (stWithinRules Q A α β M O w s T S b).2.1 h1 h2 h3 h
end QueryMachines.Tower
