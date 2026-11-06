-- Prove2me | solution 1 for QueryMachines.Tower.rout_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:12.985361+00:00
-- url     : https://prove2.me/submissions/de780f9d-45c3-4d01-a8c4-00a40351b6c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Q A α β : Type} (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β)
namespace QueryMachines.Tower
theorem _root_.solution {s : M.σ} (K : List M.σ) (h : M.out s = none) : rout M (s :: K) = none := by
  cases K
  · exact h
  · rfl
end QueryMachines.Tower
