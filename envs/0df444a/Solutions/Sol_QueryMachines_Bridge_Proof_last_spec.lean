-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.last_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:20:54.972249+00:00
-- url     : https://prove2.me/submissions/cd524ad6-7d00-4502-be03-8bbccadfafc6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_CountedToPadded_Pick
import Theorems.Thm_QueryMachines_Bridge_Proof_cand_eq
import Theorems.Thm_QueryMachines_Bridge_Proof_last_succ
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {K : ℕ → ℕ} {kf : U × U → Option U} (hk : ComputesLevels K kf) (b : U) : ∀ m : ℕ, m ≤ b.length + 1 →
    (((List.range m).filterMap (cand kf b)).getLast? = none ∧ ∀ l < m, b.length < K l) ∨
    ∃ l < m, ((List.range m).filterMap (cand kf b)).getLast? = some (unary l, (unary l, unary (K l))) ∧ K l ≤ b.length ∧ ∀ l', l < l' → l' < m → b.length < K l' := by
  intro m
  induction m with
  | zero => intro _; exact Or.inl ⟨rfl, fun l h => absurd h (Nat.not_lt_zero l)⟩
  | succ m ih =>
    intro hm
    rw [last_succ, cand_eq hk b (by omega : m ≤ b.length)]
    by_cases hK : K m ≤ b.length
    · rw [if_pos hK]
      exact Or.inr ⟨m, Nat.lt_succ_self m, rfl, hK, fun l' h1 h2 => by omega⟩
    · rw [if_neg hK]
      rcases ih (by omega) with ⟨h1, h2⟩ | ⟨l, hl, h1, h2, h3⟩
      · refine Or.inl ⟨by rw [h1]; rfl, fun l hl => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl
        · exact h2 l h
        · omega
      · refine Or.inr ⟨l, by omega, by rw [h1]; rfl, h2, fun l' g1 g2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 g2 with h | rfl
        · exact h3 l' g1 h
        · omega
end QueryMachines.Bridge.Proof
