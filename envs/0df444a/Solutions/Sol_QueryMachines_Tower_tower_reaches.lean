-- Prove2me | solution 1 for QueryMachines.Tower.tower_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:28.315003+00:00
-- url     : https://prove2.me/submissions/cdcb9a07-2a8b-4ddf-91f0-ddd1bc370602

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Chain
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
import Definitions.Def_Tower_TowerRuns

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} [HasSize Ctx] {P : Spec Ctx Q A} {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A}
  {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} {SS SI SC : ℕ} {c0 : Ctx} {f0 : Q → Option A} {tq : ℕ}
namespace QueryMachines.Tower
theorem _root_.solution {O : Q ⊕ G → Option A} {S : ℕ} {b : A} {s : (selfCall (nest Sol Inn)).σ} {own : ℕ} {L : List (Q ⊕ G)} (h : (selfCall (nest Sol Inn)).Reaches O S b s own L) :
    (tower Sol Inn).Reaches O S b s own L := by
  induction h with
  | halt h1 h2 => exact .halt h1 h2
  | step h1 h2 h3 _ ih => exact .step h1 h2 h3 ih
  | query h1 h2 h3 h4 _ ih => exact .query h1 h2 h3 h4 ih
end QueryMachines.Tower
