-- Prove2me | solution 1 for QueryMachines.Tower.up_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:41:34.076341+00:00
-- url     : https://prove2.me/submissions/cc38d06d-94ce-48fb-a362-595d6ef5c070

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Chain
import Theorems.Thm_QueryMachines_Tower_callOracle_call
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} (P : Spec Ctx Q A) (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (c0 : Ctx) (f0 : Q → Option A) (tq : ℕ)
variable {P TS TI c0 f0} [HasSize Ctx] {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A} {SS SI SC : ℕ}
omit [HasSize Ctx]
namespace QueryMachines.Tower
theorem _root_.solution (gl : G → Option A) (wg : G → ℕ) (TS : ℕ → ℕ → ℕ → ℕ) (env : List Ctx) (hC : Chain P c0 f0 env) (y : Q ⊕ G) (v : A) (hy : Sum.elim (tabs P f0 env) gl y = some v) (x : NIn Ctx Q)
    (hx : env.length ≤ ndep P x) :
    ∃ r : A ⊕ A, callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) x (upQuery env y) = some r ∧ r.elim id id = v ∧
      (Sum.elim (Sum.elim (fun _ => tq) wg) fun a' => nT P TS TI tq a' + 2) (upQuery env y) = Sum.elim (fun _ => price P TI tq env) wg y := by
  rcases y with q | g
  · rcases env with _ | ⟨c1, env'⟩
    · refine ⟨Sum.inl v, ?_, rfl, rfl⟩
      show Option.map Sum.inl (f0 q) = some (Sum.inl v)
      rw [show f0 q = some v from hy]; rfl
    · have hy' : P.tab c1 (tabs P f0 env') q = some v := hy
      refine ⟨Sum.inr v, ?_, rfl, rfl⟩
      show callOracle _ _ _ _ x (Sum.inr (Sum.inr (c1, env', q))) = _
      rw [callOracle_call _ _ ⟨⟨hC, by rw [hy']; rfl⟩, Nat.lt_of_succ_le hx⟩]
      show some (Sum.inr ((P.tab c1 (tabs P f0 env') q).getD _)) = _
      rw [hy']; rfl
  · refine ⟨Sum.inl v, ?_, rfl, rfl⟩
    show Option.map Sum.inl (gl g) = some (Sum.inl v)
    rw [show gl g = some v from hy]; rfl
end QueryMachines.Tower
