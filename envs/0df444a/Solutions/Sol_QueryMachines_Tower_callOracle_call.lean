-- Prove2me | solution 1 for QueryMachines.Tower.callOracle_call
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:36:43.185021+00:00
-- url     : https://prove2.me/submissions/f91398f5-5666-4a0e-bc7a-5eaf92a189bc

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
theorem _root_.solution {Q A α β : Type} (O : Q → Option A) {Good : α → Prop} (val : α → β) {dep : α → ℕ} {a a' : α} (h : Good a' ∧ dep a' < dep a) :
    callOracle O Good val dep a (Sum.inr a') = some (Sum.inr (val a')) := if_pos h
end QueryMachines.Tower
