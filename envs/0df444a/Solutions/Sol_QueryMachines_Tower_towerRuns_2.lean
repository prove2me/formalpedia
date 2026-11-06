-- Prove2me | solution 2 for QueryMachines.Tower.towerRuns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:51:51.345183+00:00
-- url     : https://prove2.me/submissions/0c60824d-2881-4630-89eb-d85932d75ee1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Chain
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
import Definitions.Def_Tower_TowerRuns
import Theorems.Thm_QueryMachines_Tower_nest_within
import Theorems.Thm_QueryMachines_Tower_tower_reaches
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_QueryMachines_Tower_selfCallRuns


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} [HasSize Ctx] {P : Spec Ctx Q A} {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A}
  {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} {SS SI SC : ℕ} {c0 : Ctx} {f0 : Q → Option A} {tq : ℕ}
namespace QueryMachines.Tower
theorem _root_.solution : TowerRuns := by
  intro Ctx Q G A _ P gl wg Sol Inn TS TI SS SI SC hM c f hG tq
  obtain ⟨own, L, hr, hc⟩ := selfCallRuns _ _ _ _ (nest Sol Inn) (Sum.elim f gl) (Sum.elim (fun _ => tq) wg) (nGood P c f) (nval P c f) (ndep P) (nT P TS TI tq)
    (P.lev c * (SC + 1) + SS + SI + 2) (fun x hx => nest_within hM hG x hx) (Sum.inl ([], c)) ⟨trivial, rfl⟩
  exact ⟨own, L, tower_reaches hr, hc⟩
end QueryMachines.Tower
