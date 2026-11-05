-- Prove2me | solution 1 for QueryMachines.Tower.wfQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:53:00.124078+00:00
-- url     : https://prove2.me/submissions/f1192e92-9a33-4a57-aeec-2ed31c86898f

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
theorem _root_.solution {x : Q} {v : A} (h1 : M.out s = none) (h2 : M.ask s = some x) (h3 : O x = some v) (h4 : size s ≤ S) (h : M.WithinFrom O w (M.resume s v) T S b) :
    M.WithinFrom O w s (T + w x) S b :=
  (stWithinRules Q A α β M O w s T S b).2.2 x v h1 h2 h3 h4 h
end QueryMachines.Tower
