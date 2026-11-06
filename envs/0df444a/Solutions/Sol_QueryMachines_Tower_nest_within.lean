-- Prove2me | solution 1 for QueryMachines.Tower.nest_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:39:33.801132+00:00
-- url     : https://prove2.me/submissions/6280ee89-3dad-4a7e-b27c-549e51d60228

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Chain
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
import Definitions.Def_Tower_TowerRuns
import Theorems.Thm_QueryMachines_Tower_sol_sim
import Theorems.Thm_QueryMachines_Tower_inn_sim
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_QueryMachines_Tower_chain_facts
import Theorems.Thm_QueryMachines_Tower_cost_eq


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} [HasSize Ctx] {P : Spec Ctx Q A} {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A}
  {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} {SS SI SC : ℕ} {c0 : Ctx} {f0 : Q → Option A} {tq : ℕ}
namespace QueryMachines.Tower
theorem _root_.solution (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) (x : NIn Ctx Q) (hx : nGood P c0 f0 x) :
    (nest Sol Inn).Within (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) x) (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) x (nT P TS TI tq x) (P.lev c0 * (SC + 1) + SS + SI + 2) (nval P c0 f0 x) := by
  rcases x with ⟨env, c⟩ | ⟨c, env, q⟩
  · obtain ⟨hC, rfl⟩ := hx
    obtain ⟨own, L, hr, hc⟩ := hM.sol _ _ (chain_facts hM hG env hC).1 (callCost TS TI (P.lev (parent c0 env)) (price P TI tq env)) (price P TI tq env)
    obtain ⟨own', L', hr', hc'⟩ := sol_sim (tq := tq) hM hG env hC hr
    exact ⟨own', L', hr', hc'.trans (hc.trans (le_of_eq (cost_eq TS TI _ _).symm))⟩
  · obtain ⟨hC, hs⟩ := hx
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨own, L, hr, hc⟩ := hM.inn _ _ c (chain_facts hM hG env hC.1).1 hC.2 q a ha (price P TI tq env)
    obtain ⟨own', L', hr', hc'⟩ := inn_sim (tq := tq) hM hG env hC.1 c q hr
    have hv : nval P c0 f0 (Sum.inr (c, env, q)) = a := by show (P.tab c (tabs P f0 env) q).getD _ = a; rw [ha]; rfl
    rw [hv]
    exact ⟨own', L', hr', hc'.trans hc⟩
end QueryMachines.Tower
