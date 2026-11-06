-- Prove2me | solution 1 for Sat3Graph.splitN_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:03:02.929657+00:00
-- url     : https://prove2.me/submissions/8e840569-112e-4f96-b2e1-1d7634137b0e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_General
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Split
import Theorems.Thm_Eight_Width_numFresh_toN
import Theorems.Thm_Eight_Width_stWidth
import Theorems.Thm_Eight_Width_toN_widthReduce
import Theorems.Thm_GraphProblems_exists_toN
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_satN_toN
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SplitSat_nodup_toN
import Theorems.Thm_SplitSat_satisfiable_widthReduce
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Eight.Width
namespace Sat3Graph
theorem _root_.solution {n : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) :
    (∀ C ∈ splitN n x, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n + numFresh x) ∧ (splitN n x).Nodup ∧ ((splitN n x).Sat ↔ x.Sat) := by
  obtain ⟨φ, rfl⟩ := exists_toN hx
  rw [← toN_widthReduce, numFresh_toN]
  obtain ⟨h3, -, -⟩ := stWidth n φ
  refine ⟨fun C hC => ?_, SplitSat.nodup_toN h3.2,
    (Decode.satN_toN _).trans ((SplitSat.satisfiable_widthReduce φ).trans (Decode.satN_toN φ).symm)⟩
  obtain ⟨⟨C', hC', hl'⟩, h⟩ := Decode.mem_toN hC
  exact ⟨hl' ▸ h3.1 C' hC', h⟩
end Sat3Graph
