-- Prove2me | solution 1 for SizeCircuit.addValue_addStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:42:11.44677+00:00
-- url     : https://prove2.me/submissions/de0f3d0e-9f89-4527-b3cc-387be8b68b0d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_SizeCircuit_addStep_three
import Theorems.Thm_SizeCircuit_addStep_two
import Theorems.Thm_SizeCircuit_addStep_one
import Theorems.Thm_SizeCircuit_fullAdder_spec
import Theorems.Thm_SizeCircuit_halfAdder_spec
import Theorems.Thm_SizeCircuit_onesAmong_nil
import Theorems.Thm_SizeCircuit_onesAmong_cons
import Theorems.Thm_SizeCircuit_addValue_mk
import Theorems.Thm_SizeCircuit_addValue_push
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_append
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (v : ℕ → Bool) (n : ℕ) (st : AddState) (h : Obeys v n (addStep n st).2.2.2) :
    Obeys v n st.2.2.2 ∧ addValue v (addStep n st) = addValue v st := by
  obtain ⟨cur, nxt, dig, K⟩ := st
  rcases cur with _ | ⟨a, _ | ⟨u, _ | ⟨w, r⟩⟩⟩
  · exact ⟨h, rfl⟩
  · refine ⟨h, ?_⟩
    rw [addStep_one, addValue_push, addValue_mk, onesAmong_cons, onesAmong_nil, Nat.add_zero]
  · rw [addStep_two] at h ⊢
    obtain ⟨hK, hA⟩ := (obeys_append v n K _).1 h
    have e := halfAdder_spec v _ a u hA
    refine ⟨hK, ?_⟩
    rw [addValue_push, addValue_mk, onesAmong_cons, onesAmong_cons, onesAmong_cons, onesAmong_nil]
    congr 2
    omega
  · rw [addStep_three] at h ⊢
    obtain ⟨hK, hA⟩ := (obeys_append v n K _).1 h
    have e := fullAdder_spec v _ a u w hA
    refine ⟨hK, ?_⟩
    rw [addValue_mk, addValue_mk, onesAmong_cons, onesAmong_cons, onesAmong_cons, onesAmong_cons, onesAmong_cons]
    congr 2
    omega
end SizeCircuit
