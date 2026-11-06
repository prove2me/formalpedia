-- Prove2me | solution 1 for QueryMachines.Tower.cost_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:11.942808+00:00
-- url     : https://prove2.me/submissions/837fed07-5083-4ad2-bda9-409edb136fcc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Chain

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} (P : Spec Ctx Q A) (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (c0 : Ctx) (f0 : Q → Option A) (tq : ℕ)
namespace QueryMachines.Tower
theorem _root_.solution (l t : ℕ) : cost TS TI l t = TS l (callCost TS TI l t) t := by cases l <;> rfl
end QueryMachines.Tower
