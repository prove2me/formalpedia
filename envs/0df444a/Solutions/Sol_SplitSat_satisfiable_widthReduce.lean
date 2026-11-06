-- Prove2me | solution 1 for SplitSat.satisfiable_widthReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:36.526983+00:00
-- url     : https://prove2.me/submissions/faa6b5e3-4bd3-4336-b96e-576174cf8ed0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_SplitSat_Leaf
import Theorems.Thm_Eight_Width_stExtend
import Theorems.Thm_Eight_Width_stRestrict


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Eight.Width GraphProblems
namespace SplitSat
theorem _root_.solution {n : ℕ} (φ : Sat3.CNF n) : Sat3.Satisfiable (widthReduce φ) ↔ Sat3.Satisfiable φ := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨fun i => b (Fin.castAdd (numFresh φ) i), stRestrict n φ b hb⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, ⟨hb, -⟩, -⟩ := stExtend n φ a ha
    exact ⟨b, hb⟩
end SplitSat
