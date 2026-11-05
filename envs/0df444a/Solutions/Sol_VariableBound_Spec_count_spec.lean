-- Prove2me | solution 1 for VariableBound.Spec.count_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:31:43.279737+00:00
-- url     : https://prove2.me/submissions/8199c937-afee-4d0b-94ae-68babf4c5182

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Spec
import Theorems.Thm_VariableBound_Spec_length_filter_range
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Spec
namespace VariableBound.Spec
theorem _root_.solution (P : ℕ → Prop) (p : ℕ → Bool) (N : ℕ) (hp : ∀ j, p j = true ↔ ¬ P j) (up : ∀ j, P j → P (j + 1)) (hN : ∃ j ≤ N, P j) :
    P ((List.range N).filter p).length ∧ ∀ j < ((List.range N).filter p).length, ¬ P j := by
  classical
  obtain ⟨j₀, hj₀, hP⟩ := hN
  have hex : ∃ j, P j := ⟨j₀, hP⟩
  have hk : Nat.find hex ≤ N := (Nat.find_min' hex hP).trans hj₀
  have hmono : ∀ j, Nat.find hex ≤ j → P j := fun j hj => Nat.le_induction (Nat.find_spec hex) (fun i _ hi => up i hi) j hj
  have hlen : ((List.range N).filter p).length = Nat.find hex := by
    rw [length_filter_range p N (Nat.find hex) fun j _ => (hp j).trans ⟨fun h => not_le.1 fun hle => h (hmono j hle), fun h => Nat.find_min hex h⟩]
    exact min_eq_right hk
  rw [hlen]
  exact ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
end VariableBound.Spec
