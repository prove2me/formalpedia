-- Prove2me | solution 1 for Sat3Graph.sat_iff_cntN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:35:19.260723+00:00
-- url     : https://prove2.me/submissions/63ece504-e6b3-4915-b6a0-09e5aaeefbe0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_General
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Split
import Theorems.Thm_Eight_Width_holds_congr
import Theorems.Thm_SizeCircuit_ext_of_lt
import Theorems.Thm_SizeCircuit_holds_congr


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Eight.Width
namespace Sat3Graph
theorem _root_.solution {N : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < N) : x.Sat ↔ cntN N x ≠ 0 := by
  unfold cntN
  rw [← Nat.pos_iff_ne_zero, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a i.1, Finset.mem_univ _, ?_⟩
    exact (SizeCircuit.holds_congr (a := ext fun i : Fin N => a i.1) (a' := a) fun C hC l hl => by
      rw [SizeCircuit.ext_of_lt _ (hx C hC l hl)]).2 ha
  · rintro ⟨b, -, hb⟩
    exact ⟨ext b, hb⟩
end Sat3Graph
