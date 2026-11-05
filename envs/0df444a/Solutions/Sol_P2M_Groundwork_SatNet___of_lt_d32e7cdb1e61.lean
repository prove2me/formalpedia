-- Prove2me | solution 1 for P2M_Groundwork_SatNet___of_lt_d32e7cdb1e61
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:56:32.632804+00:00
-- url     : https://prove2.me/submissions/ff5f0f05-3ad7-4e8a-ae74-a87c90f5ea6d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution {a b : Fin g} (h : a < b) (z z' : Sl μ k → Bool) :
    (net φ g μ k).Ψ a b z z' = if ∀ s s', Link φ (a, s) (b, s') → z s = z' s' then 1 else 0 := by
  have hba : ¬ b < a := not_lt.2 h.le
  simp only [Network.Ψ, Network.lab, net, min_eq_left h.le, max_eq_right h.le, if_pos h, if_neg hba]
  set θ₀ : Sl μ k → Bool := fun s => if Out φ a b s then z s else false with hθ₀
  rw [Finset.sum_eq_single θ₀]
  · have h1 : ∀ s, Out φ a b s → z s = θ₀ s := fun s hs => by simp [hθ₀, hs]
    rw [if_pos h1, one_mul]
    refine if_congr ⟨fun H s s' hl => ?_, fun H s s' hl => ?_⟩ rfl rfl
    · rw [H s s' hl, ← h1 s ⟨s', hl⟩]
    · rw [← h1 s ⟨s', hl⟩, H s s' hl]
  · intro θ hθ hne
    rw [if_neg, zero_mul]
    intro hA
    apply hne
    funext s
    by_cases hs : Out φ a b s
    · simp [hθ₀, hs, hA s hs]
    · have := Fintype.mem_piFinset.1 hθ s
      simp only [hs, ite_false, mem_singleton] at this
      simp [hθ₀, hs, this]
  · intro hnot
    exfalso
    apply hnot
    unfold tuples
    rw [Fintype.mem_piFinset]
    intro s
    by_cases hs : Out φ a b s <;> simp [hθ₀, hs]
end Groundwork.SatNet
